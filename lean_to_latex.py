#!/usr/bin/env python3
"""
Convert a Lean 4 file with documentation comments to a PDF.
- Code blocks get Pygments-style syntax highlighting via minted
- Documentation comments (/-! ... -/ and /- ... -/) become prose
- Inline comments stay with the code
"""

import re
import subprocess
import sys
from pathlib import Path

def parse_lean_file(content: str) -> list:
    """
    Parse Lean file into segments of (type, content).
    Types: 'doc' for documentation, 'code' for Lean code.
    """
    segments = []
    
    # Pattern for documentation comments: /-! ... -/ or /- ... -/
    doc_pattern = re.compile(r'/\-[\!]?\s*(.*?)\-/', re.DOTALL)
    
    pos = 0
    for match in doc_pattern.finditer(content):
        # Add any code before this documentation block
        if match.start() > pos:
            code = content[pos:match.start()].strip()
            if code:
                segments.append(('code', code))
        
        # Add the documentation
        doc_content = match.group(1).strip()
        if doc_content:
            segments.append(('doc', doc_content))
        
        pos = match.end()
    
    # Add any remaining code
    if pos < len(content):
        code = content[pos:].strip()
        if code:
            segments.append(('code', code))
    
    return segments

def escape_latex(text: str) -> str:
    """Escape special LaTeX characters, but preserve Unicode."""
    # Only escape ASCII special characters that LaTeX needs escaped
    # Don't touch Unicode characters (Greek letters, logic symbols, etc.)
    text = text.replace('&', '\\&')
    text = text.replace('%', '\\%')
    text = text.replace('$', '\\$')
    text = text.replace('#', '\\#')
    text = text.replace('_', '\\_')
    text = text.replace('{', '\\{')
    text = text.replace('}', '\\}')
    text = text.replace('~', '\\textasciitilde{}')
    text = text.replace('^', '\\textasciicircum{}')
    return text

def process_inline_formatting(text: str) -> str:
    """Process inline markdown formatting (bold, italic, code, links)."""
    # Protect code spans first (we'll restore them later)
    code_spans = []
    def save_code(match):
        code_spans.append(match.group(1))
        return f"__CODE_SPAN_{len(code_spans)-1}__"
    
    text = re.sub(r'`([^`]+)`', save_code, text)
    
    # Now escape LaTeX special chars in the remaining text
    # But we need to be careful with the placeholders
    parts = re.split(r'(__CODE_SPAN_\d+__)', text)
    escaped_parts = []
    for part in parts:
        if part.startswith('__CODE_SPAN_'):
            escaped_parts.append(part)
        else:
            escaped_parts.append(escape_latex(part))
    text = ''.join(escaped_parts)
    
    # Restore code spans as \texttt
    for i, code in enumerate(code_spans):
        escaped_code = escape_latex(code)
        text = text.replace(f"__CODE_SPAN_{i}__", f"\\texttt{{{escaped_code}}}")
    
    # Bold and italic
    text = re.sub(r'\*\*(.+?)\*\*', r'\\textbf{\1}', text)
    text = re.sub(r'\*(.+?)\*', r'\\textit{\1}', text)
    
    # Convert URLs to hyperlinks
    text = re.sub(r'(https?://[^\s\)]+)', r'\\url{\1}', text)
    
    # Checkmarks and crosses
    text = text.replace('✓', '$\\checkmark$')
    text = text.replace('✗', '$\\times$')
    
    return text

def convert_markdown_to_latex(text: str) -> str:
    """Convert markdown text to LaTeX with proper formatting."""
    lines = text.split('\n')
    result = []
    
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        
        # Headers
        if stripped.startswith('#### '):
            result.append(f"\\paragraph{{{process_inline_formatting(stripped[5:])}}}")
            result.append('')
            i += 1
            continue
        elif stripped.startswith('### '):
            result.append(f"\\subsubsection*{{{process_inline_formatting(stripped[4:])}}}")
            result.append('')
            i += 1
            continue
        elif stripped.startswith('## '):
            result.append(f"\\subsection*{{{process_inline_formatting(stripped[3:])}}}")
            result.append('')
            i += 1
            continue
        elif stripped.startswith('# '):
            result.append(f"\\section*{{{process_inline_formatting(stripped[2:])}}}")
            result.append('')
            i += 1
            continue
        
        # Code blocks (``` ... ```)
        if stripped.startswith('```'):
            lang = stripped[3:].strip()
            code_lines = []
            i += 1
            while i < len(lines) and not lines[i].strip().startswith('```'):
                code_lines.append(lines[i])
                i += 1
            i += 1  # skip closing ```
            
            # Check if this looks like a visual diagram (contains box-drawing characters)
            is_visual_diagram = any(any(c in line for c in '┌┐└┘├┤│─┬┴┼') for line in code_lines)
            
            # For visual diagrams, look back to include "Visual representation:" header
            if is_visual_diagram:
                # Look back to find "Visual representation:" header (skip empty lines)
                lines_to_pull_back = []
                found_header = False
                for lookback_idx in range(min(5, len(result))):
                    idx = len(result) - 1 - lookback_idx
                    if idx >= 0:
                        line_text = result[idx]
                        # Check if this line contains "Visual representation"
                        if 'Visual representation' in line_text:
                            # Include this line and everything after it
                            lines_to_pull_back = result[idx:]
                            result = result[:idx]
                            found_header = True
                            break
                        # Stop if we hit non-empty non-header content
                        elif line_text.strip() and not line_text.strip().startswith('\\textbf{'):
                            # Don't look back further if we hit substantial content
                            break
                
                # Use minipage for absolute no-break guarantee
                if found_header:
                    result.append('\\begin{minipage}{\\linewidth}')
                    result.extend(lines_to_pull_back)
                    result.append('')  # Spacing after header
            
            # Use minted for code blocks
            if lang in ['lean', 'lean4']:
                result.append('\\begin{minted}[fontsize=\\small,bgcolor=gray!10]{lean4}')
            else:
                result.append('\\begin{minted}[fontsize=\\small,bgcolor=gray!10]{text}')
            result.extend(code_lines)
            result.append('\\end{minted}')
            
            if is_visual_diagram and found_header:
                result.append('\\end{minipage}')
            
            result.append('')
            continue
        
        # Block quotes
        if stripped.startswith('>'):
            quote_lines = []
            while i < len(lines) and lines[i].strip().startswith('>'):
                quote_content = lines[i].strip()[1:].strip()
                quote_lines.append(process_inline_formatting(quote_content))
                i += 1
            result.append('\\begin{quote}')
            result.append(' '.join(quote_lines))
            result.append('\\end{quote}')
            result.append('')
            continue
        
        # Tables
        if stripped.startswith('|') and i + 1 < len(lines) and '---' in lines[i + 1]:
            # Parse table
            header_line = stripped
            separator_line = lines[i + 1].strip()
            i += 2
            
            data_lines = []
            while i < len(lines) and lines[i].strip().startswith('|'):
                data_lines.append(lines[i].strip())
                i += 1
            
            # Extract columns
            headers = [h.strip() for h in header_line.split('|')[1:-1]]
            num_cols = len(headers)
            
            # Create LaTeX table
            result.append('\\begin{center}')
            result.append('\\begin{tabular}{' + 'l' * num_cols + '}')
            result.append('\\hline')
            
            # Header row
            header_cells = [process_inline_formatting(h) for h in headers]
            result.append(' & '.join(header_cells) + ' \\\\')
            result.append('\\hline')
            
            # Data rows
            for data_line in data_lines:
                cells = [c.strip() for c in data_line.split('|')[1:-1]]
                processed_cells = [process_inline_formatting(c) for c in cells]
                result.append(' & '.join(processed_cells) + ' \\\\')
            
            result.append('\\hline')
            result.append('\\end{tabular}')
            result.append('\\end{center}')
            result.append('')
            continue
        
        # Bullet lists
        if stripped.startswith('- ') or stripped.startswith('* '):
            result.append('\\begin{itemize}')
            while i < len(lines):
                current = lines[i].strip()
                if current.startswith('- ') or current.startswith('* '):
                    item_text = current[2:]
                    # Check for continuation lines (indented)
                    i += 1
                    while i < len(lines) and lines[i].startswith('  ') and not lines[i].strip().startswith('-'):
                        item_text += ' ' + lines[i].strip()
                        i += 1
                    result.append(f"  \\item {process_inline_formatting(item_text)}")
                elif current == '':
                    i += 1
                    # Check if list continues
                    if i < len(lines) and (lines[i].strip().startswith('- ') or lines[i].strip().startswith('* ')):
                        continue
                    else:
                        break
                else:
                    break
            result.append('\\end{itemize}')
            result.append('')
            continue
        
        # Numbered lists
        if re.match(r'^\d+\.\s', stripped):
            result.append('\\begin{enumerate}')
            while i < len(lines):
                current = lines[i].strip()
                match = re.match(r'^(\d+)\.\s(.+)$', current)
                if match:
                    item_text = match.group(2)
                    # Check for continuation/sub-items
                    i += 1
                    while i < len(lines) and lines[i].startswith('  ') and not re.match(r'^\s*\d+\.', lines[i]):
                        sub = lines[i].strip()
                        if sub.startswith('- '):
                            # Sub-bullet - just append for now
                            item_text += f" ({sub[2:]})"
                        else:
                            item_text += ' ' + sub
                        i += 1
                    result.append(f"  \\item {process_inline_formatting(item_text)}")
                elif current == '':
                    i += 1
                    if i < len(lines) and re.match(r'^\d+\.\s', lines[i].strip()):
                        continue
                    else:
                        break
                else:
                    break
            result.append('\\end{enumerate}')
            result.append('')
            continue
        
        # Description-like lists (Key: Value format on separate lines)
        # Detect pattern: **Key:** Value
        if re.match(r'^\*\*[^*]+:\*\*\s*.+$', stripped):
            # Collect all description items
            desc_items = []
            while i < len(lines):
                current = lines[i].strip()
                match = re.match(r'^\*\*([^*]+):\*\*\s*(.+)$', current)
                if match:
                    desc_items.append((match.group(1), match.group(2)))
                    i += 1
                elif current == '':
                    i += 1
                    # Check if more description items follow
                    if i < len(lines) and re.match(r'^\*\*[^*]+:\*\*', lines[i].strip()):
                        continue
                    else:
                        break
                else:
                    break
            
            # Format as description list
            result.append('\\begin{description}')
            for key, value in desc_items:
                escaped_key = process_inline_formatting(key)
                escaped_value = process_inline_formatting(value)
                result.append(f"  \\item[{escaped_key}] {escaped_value}")
            result.append('\\end{description}')
            result.append('')
            continue
        
        # Empty line = paragraph break
        if stripped == '':
            result.append('')
            i += 1
            continue
        
        # Regular paragraph text
        para_lines = []
        while i < len(lines):
            current = lines[i].strip()
            # Stop at structural elements
            if (current == '' or 
                current.startswith('#') or 
                current.startswith('```') or
                current.startswith('>') or
                current.startswith('|') or
                current.startswith('- ') or
                current.startswith('* ') or
                re.match(r'^\d+\.\s', current) or
                re.match(r'^\*\*[^*]+:\*\*\s*.+$', current)):
                break
            para_lines.append(current)
            i += 1
        
        if para_lines:
            para_text = ' '.join(para_lines)
            result.append(process_inline_formatting(para_text))
            result.append('')
        else:
            # Safety: if we collected no lines, we must still advance
            # to avoid infinite loop
            i += 1
    
    return '\n'.join(result)

def generate_latex(segments: list, title: str = "Lean Formalization") -> str:
    """Generate LaTeX document from parsed segments."""
    
    latex = r'''\documentclass[11pt,a4paper]{article}
\usepackage{fontspec}
\usepackage{unicode-math}
\usepackage{minted}
\usepackage{geometry}
\usepackage{parskip}
\usepackage{hyperref}
\usepackage{booktabs}
\usepackage{enumitem}

% Set fonts - Libertinus has excellent Unicode support and Times-like appearance
\setmainfont{Libertinus Serif}
\setmonofont{DejaVu Sans Mono}[Scale=0.85]
\setmathfont{Libertinus Math}

\geometry{margin=2.5cm}

% Configure hyperlinks
\hypersetup{
    colorlinks=true,
    linkcolor=blue,
    urlcolor=blue,
    citecolor=blue
}

% Configure minted for Lean code
\setminted{
    style=friendly
}
\setminted[lean4]{
    fontsize=\small,
    breaklines=true,
    linenos=false,
    bgcolor=gray!5,
    frame=single,
    framesep=2mm,
    samepage=true
}

% Tighter lists
\setlist{nosep}

\title{''' + escape_latex(title) + r'''}
\author{Huub Vromen}
\date{}

\begin{document}
\maketitle

'''
    
    for seg_type, content in segments:
        if seg_type == 'doc':
            # Convert documentation to LaTeX prose
            converted = convert_markdown_to_latex(content)
            latex += converted + '\n\n'
        else:
            # Code block with syntax highlighting
            if content.strip():
                # Use minipage to prevent page breaks within code blocks
                latex += r'\begin{minipage}{\linewidth}' + '\n'
                latex += r'\begin{minted}{lean4}' + '\n'
                latex += content + '\n'
                latex += r'\end{minted}' + '\n'
                latex += r'\end{minipage}' + '\n\n'
    
    latex += r'\end{document}'
    return latex

def main():
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Convert a Lean 4 file with documentation comments to LaTeX with syntax highlighting.'
    )
    parser.add_argument('input_file', help='Path to the Lean file to convert')
    parser.add_argument('-o', '--output', help='Output directory (default: current directory)', default='.')
    parser.add_argument('-t', '--title', help='Document title (default: derived from filename)')
    parser.add_argument('--no-pdf', action='store_true', help='Generate LaTeX only, do not compile to PDF')
    
    args = parser.parse_args()
    
    input_path = Path(args.input_file)
    if not input_path.exists():
        print(f"Error: File not found: {args.input_file}")
        sys.exit(1)
    
    output_dir = Path(args.output)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    output_name = input_path.stem
    
    # Read input file
    with open(input_path, 'r') as f:
        content = f.read()
    
    # Parse into segments
    segments = parse_lean_file(content)
    
    # Generate LaTeX
    if args.title:
        title = args.title
    else:
        # Derive title from filename
        title = output_name.replace('_', ' ').title()
    
    latex = generate_latex(segments, title)
    
    # Write LaTeX file
    tex_file = output_dir / f"{output_name}.tex"
    with open(tex_file, 'w') as f:
        f.write(latex)
    
    print(f"Generated LaTeX file: {tex_file}")
    
    if args.no_pdf:
        print(f"Compile with: lualatex -shell-escape {output_name}.tex")
        return
    
    # Compile to PDF with LuaLaTeX
    print("Compiling to PDF with LuaLaTeX...")
    
    # Set environment variable for minted v3
    import os
    env = os.environ.copy()
    env['TEXMF_OUTPUT_DIRECTORY'] = str(output_dir.resolve())
    
    result = subprocess.run(
        ['lualatex', '-shell-escape', '-interaction=nonstopmode', f'{output_name}.tex'],
        cwd=str(output_dir),
        capture_output=True,
        env=env
    )
    
    if result.returncode != 0:
        print("First pass completed (may have warnings)")
    
    # Run again for references
    subprocess.run(
        ['lualatex', '-shell-escape', '-interaction=nonstopmode', f'{output_name}.tex'],
        cwd=str(output_dir),
        capture_output=True,
        env=env
    )
    
    pdf_file = output_dir / f"{output_name}.pdf"
    
    # Clean up intermediate files (do this regardless of success/failure)
    import shutil
    for ext in ['aux', 'log', 'out', 'toc', 'lof', 'lot', 'fls', 'fdb_latexmk']:
        intermediate = output_dir / f"{output_name}.{ext}"
        if intermediate.exists():
            intermediate.unlink()
    
    # Clean up minted cache files
    for minted_file in output_dir.glob('*.minted'):
        minted_file.unlink()
    
    # Clean up minted cache directory (primary target)
    minted_dir = output_dir / f"_minted-{output_name}"
    if minted_dir.exists() and minted_dir.is_dir():
        shutil.rmtree(minted_dir)
    
    # Clean up any other _minted-* directories (from previous runs)
    for minted_path in output_dir.glob('_minted-*'):
        if minted_path.is_dir():
            shutil.rmtree(minted_path)
    
    # Also check for plain "_minted" directory (some versions create this)
    plain_minted = output_dir / "_minted"
    if plain_minted.exists() and plain_minted.is_dir():
        shutil.rmtree(plain_minted)
    
    if pdf_file.exists():
        print(f"PDF created: {pdf_file}")
        print("Cleaned up intermediate files")
    else:
        print("PDF compilation failed. Check the LaTeX log file.")
        print("Cleaned up intermediate files")
        log_file = output_dir / f"{output_name}.log"
        if log_file.exists():
            with open(log_file, 'r', errors='ignore') as f:
                log_content = f.read()
                if '!' in log_content:
                    errors = [line for line in log_content.split('\n') if line.startswith('!')]
                    print("Errors found:")
                    for err in errors[:10]:
                        print(err)
#!/usr/bin/env python3
"""
Convert a Lean 4 file with documentation comments to a PDF.
- Code blocks get Pygments-style syntax highlighting via minted
- Documentation comments (/-! ... -/ and /- ... -/) become prose
- Inline comments stay with the code
"""

import re
import subprocess
import sys
from pathlib import Path

def parse_lean_file(content: str) -> list:
    """
    Parse Lean file into segments of (type, content).
    Types: 'doc' for documentation, 'code' for Lean code.
    """
    segments = []
    
    # Pattern for documentation comments: /-! ... -/ or /- ... -/
    doc_pattern = re.compile(r'/\-[\!]?\s*(.*?)\-/', re.DOTALL)
    
    pos = 0
    for match in doc_pattern.finditer(content):
        # Add any code before this documentation block
        if match.start() > pos:
            code = content[pos:match.start()].strip()
            if code:
                segments.append(('code', code))
        
        # Add the documentation
        doc_content = match.group(1).strip()
        if doc_content:
            segments.append(('doc', doc_content))
        
        pos = match.end()
    
    # Add any remaining code
    if pos < len(content):
        code = content[pos:].strip()
        if code:
            segments.append(('code', code))
    
    return segments

def escape_latex(text: str) -> str:
    """Escape special LaTeX characters, but preserve Unicode."""
    # Only escape ASCII special characters that LaTeX needs escaped
    # Don't touch Unicode characters (Greek letters, logic symbols, etc.)
    text = text.replace('&', '\\&')
    text = text.replace('%', '\\%')
    text = text.replace('$', '\\$')
    text = text.replace('#', '\\#')
    text = text.replace('_', '\\_')
    text = text.replace('{', '\\{')
    text = text.replace('}', '\\}')
    text = text.replace('~', '\\textasciitilde{}')
    text = text.replace('^', '\\textasciicircum{}')
    return text

def process_inline_formatting(text: str) -> str:
    """Process inline markdown formatting (bold, italic, code, links)."""
    # Protect code spans first (we'll restore them later)
    code_spans = []
    def save_code(match):
        code_spans.append(match.group(1))
        return f"__CODE_SPAN_{len(code_spans)-1}__"
    
    text = re.sub(r'`([^`]+)`', save_code, text)
    
    # Now escape LaTeX special chars in the remaining text
    # But we need to be careful with the placeholders
    parts = re.split(r'(__CODE_SPAN_\d+__)', text)
    escaped_parts = []
    for part in parts:
        if part.startswith('__CODE_SPAN_'):
            escaped_parts.append(part)
        else:
            escaped_parts.append(escape_latex(part))
    text = ''.join(escaped_parts)
    
    # Restore code spans as \texttt
    for i, code in enumerate(code_spans):
        escaped_code = escape_latex(code)
        text = text.replace(f"__CODE_SPAN_{i}__", f"\\texttt{{{escaped_code}}}")
    
    # Bold and italic
    text = re.sub(r'\*\*(.+?)\*\*', r'\\textbf{\1}', text)
    text = re.sub(r'\*(.+?)\*', r'\\textit{\1}', text)
    
    # Convert URLs to hyperlinks
    text = re.sub(r'(https?://[^\s\)]+)', r'\\url{\1}', text)
    
    # Checkmarks and crosses
    text = text.replace('✓', '$\\checkmark$')
    text = text.replace('✗', '$\\times$')
    
    return text

def convert_markdown_to_latex(text: str) -> str:
    """Convert markdown text to LaTeX with proper formatting."""
    lines = text.split('\n')
    result = []
    
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        
        # Headers
        if stripped.startswith('#### '):
            result.append(f"\\paragraph{{{process_inline_formatting(stripped[5:])}}}")
            result.append('')
            i += 1
            continue
        elif stripped.startswith('### '):
            result.append(f"\\subsubsection*{{{process_inline_formatting(stripped[4:])}}}")
            result.append('')
            i += 1
            continue
        elif stripped.startswith('## '):
            result.append(f"\\subsection*{{{process_inline_formatting(stripped[3:])}}}")
            result.append('')
            i += 1
            continue
        elif stripped.startswith('# '):
            result.append(f"\\section*{{{process_inline_formatting(stripped[2:])}}}")
            result.append('')
            i += 1
            continue
        
        # Code blocks (``` ... ```)
        if stripped.startswith('```'):
            lang = stripped[3:].strip()
            code_lines = []
            i += 1
            while i < len(lines) and not lines[i].strip().startswith('```'):
                code_lines.append(lines[i])
                i += 1
            i += 1  # skip closing ```
            
            # Check if this looks like a visual diagram (contains box-drawing characters)
            is_visual_diagram = any(any(c in line for c in '┌┐└┘├┤│─┬┴┼') for line in code_lines)
            
            # For visual diagrams, look back to include "Visual representation:" header
            if is_visual_diagram:
                # Look back to find "Visual representation:" header (skip empty lines)
                lines_to_pull_back = []
                found_header = False
                for lookback_idx in range(min(5, len(result))):
                    idx = len(result) - 1 - lookback_idx
                    if idx >= 0:
                        line_text = result[idx]
                        # Check if this line contains "Visual representation"
                        if 'Visual representation' in line_text:
                            # Include this line and everything after it
                            lines_to_pull_back = result[idx:]
                            result = result[:idx]
                            found_header = True
                            break
                        # Stop if we hit non-empty non-header content
                        elif line_text.strip() and not line_text.strip().startswith('\\textbf{'):
                            # Don't look back further if we hit substantial content
                            break
                
                # Use minipage for absolute no-break guarantee
                if found_header:
                    result.append('\\begin{minipage}{\\linewidth}')
                    result.extend(lines_to_pull_back)
                    result.append('')  # Spacing after header
            
            # Use minted for code blocks
            if lang in ['lean', 'lean4']:
                result.append('\\begin{minted}[fontsize=\\small,bgcolor=gray!10]{lean4}')
            else:
                result.append('\\begin{minted}[fontsize=\\small,bgcolor=gray!10]{text}')
            result.extend(code_lines)
            result.append('\\end{minted}')
            
            if is_visual_diagram and found_header:
                result.append('\\end{minipage}')
            
            result.append('')
            continue
        
        # Block quotes
        if stripped.startswith('>'):
            quote_lines = []
            while i < len(lines) and lines[i].strip().startswith('>'):
                quote_content = lines[i].strip()[1:].strip()
                quote_lines.append(process_inline_formatting(quote_content))
                i += 1
            result.append('\\begin{quote}')
            result.append(' '.join(quote_lines))
            result.append('\\end{quote}')
            result.append('')
            continue
        
        # Tables
        if stripped.startswith('|') and i + 1 < len(lines) and '---' in lines[i + 1]:
            # Parse table
            header_line = stripped
            separator_line = lines[i + 1].strip()
            i += 2
            
            data_lines = []
            while i < len(lines) and lines[i].strip().startswith('|'):
                data_lines.append(lines[i].strip())
                i += 1
            
            # Extract columns
            headers = [h.strip() for h in header_line.split('|')[1:-1]]
            num_cols = len(headers)
            
            # Create LaTeX table
            result.append('\\begin{center}')
            result.append('\\begin{tabular}{' + 'l' * num_cols + '}')
            result.append('\\hline')
            
            # Header row
            header_cells = [process_inline_formatting(h) for h in headers]
            result.append(' & '.join(header_cells) + ' \\\\')
            result.append('\\hline')
            
            # Data rows
            for data_line in data_lines:
                cells = [c.strip() for c in data_line.split('|')[1:-1]]
                processed_cells = [process_inline_formatting(c) for c in cells]
                result.append(' & '.join(processed_cells) + ' \\\\')
            
            result.append('\\hline')
            result.append('\\end{tabular}')
            result.append('\\end{center}')
            result.append('')
            continue
        
        # Bullet lists
        if stripped.startswith('- ') or stripped.startswith('* '):
            result.append('\\begin{itemize}')
            while i < len(lines):
                current = lines[i].strip()
                if current.startswith('- ') or current.startswith('* '):
                    item_text = current[2:]
                    # Check for continuation lines (indented)
                    i += 1
                    while i < len(lines) and lines[i].startswith('  ') and not lines[i].strip().startswith('-'):
                        item_text += ' ' + lines[i].strip()
                        i += 1
                    result.append(f"  \\item {process_inline_formatting(item_text)}")
                elif current == '':
                    i += 1
                    # Check if list continues
                    if i < len(lines) and (lines[i].strip().startswith('- ') or lines[i].strip().startswith('* ')):
                        continue
                    else:
                        break
                else:
                    break
            result.append('\\end{itemize}')
            result.append('')
            continue
        
        # Numbered lists
        if re.match(r'^\d+\.\s', stripped):
            result.append('\\begin{enumerate}')
            while i < len(lines):
                current = lines[i].strip()
                match = re.match(r'^(\d+)\.\s(.+)$', current)
                if match:
                    item_text = match.group(2)
                    # Check for continuation/sub-items
                    i += 1
                    while i < len(lines) and lines[i].startswith('  ') and not re.match(r'^\s*\d+\.', lines[i]):
                        sub = lines[i].strip()
                        if sub.startswith('- '):
                            # Sub-bullet - just append for now
                            item_text += f" ({sub[2:]})"
                        else:
                            item_text += ' ' + sub
                        i += 1
                    result.append(f"  \\item {process_inline_formatting(item_text)}")
                elif current == '':
                    i += 1
                    if i < len(lines) and re.match(r'^\d+\.\s', lines[i].strip()):
                        continue
                    else:
                        break
                else:
                    break
            result.append('\\end{enumerate}')
            result.append('')
            continue
        
        # Description-like lists (Key: Value format on separate lines)
        # Detect pattern: **Key:** Value
        if re.match(r'^\*\*[^*]+:\*\*\s*.+$', stripped):
            # Collect all description items
            desc_items = []
            while i < len(lines):
                current = lines[i].strip()
                match = re.match(r'^\*\*([^*]+):\*\*\s*(.+)$', current)
                if match:
                    desc_items.append((match.group(1), match.group(2)))
                    i += 1
                elif current == '':
                    i += 1
                    # Check if more description items follow
                    if i < len(lines) and re.match(r'^\*\*[^*]+:\*\*', lines[i].strip()):
                        continue
                    else:
                        break
                else:
                    break
            
            # Format as description list
            result.append('\\begin{description}')
            for key, value in desc_items:
                escaped_key = process_inline_formatting(key)
                escaped_value = process_inline_formatting(value)
                result.append(f"  \\item[{escaped_key}] {escaped_value}")
            result.append('\\end{description}')
            result.append('')
            continue
        
        # Empty line = paragraph break
        if stripped == '':
            result.append('')
            i += 1
            continue
        
        # Regular paragraph text
        para_lines = []
        while i < len(lines):
            current = lines[i].strip()
            # Stop at structural elements
            if (current == '' or 
                current.startswith('#') or 
                current.startswith('```') or
                current.startswith('>') or
                current.startswith('|') or
                current.startswith('- ') or
                current.startswith('* ') or
                re.match(r'^\d+\.\s', current) or
                re.match(r'^\*\*[^*]+:\*\*\s*.+$', current)):
                break
            para_lines.append(current)
            i += 1
        
        if para_lines:
            para_text = ' '.join(para_lines)
            result.append(process_inline_formatting(para_text))
            result.append('')
        else:
            # Safety: if we collected no lines, we must still advance
            # to avoid infinite loop
            i += 1
    
    return '\n'.join(result)

def generate_latex(segments: list, title: str = "Lean Formalization") -> str:
    """Generate LaTeX document from parsed segments."""
    
    latex = r'''\documentclass[11pt,a4paper]{article}
\usepackage{fontspec}
\usepackage{unicode-math}
\usepackage{minted}
\usepackage{geometry}
\usepackage{parskip}
\usepackage{hyperref}
\usepackage{booktabs}
\usepackage{enumitem}

% Set fonts - Libertinus has excellent Unicode support and Times-like appearance
\setmainfont{Libertinus Serif}
\setmonofont{DejaVu Sans Mono}[Scale=0.85]
\setmathfont{Libertinus Math}

\geometry{margin=2.5cm}

% Configure hyperlinks
\hypersetup{
    colorlinks=true,
    linkcolor=blue,
    urlcolor=blue,
    citecolor=blue
}

% Configure minted for Lean code
\setminted{
    style=friendly
}
\setminted[lean4]{
    fontsize=\small,
    breaklines=true,
    linenos=false,
    bgcolor=gray!5,
    frame=single,
    framesep=2mm,
    samepage=true
}

% Tighter lists
\setlist{nosep}

\title{''' + escape_latex(title) + r'''}
\author{Huub Vromen}
\date{}

\begin{document}
\maketitle

'''
    
    for seg_type, content in segments:
        if seg_type == 'doc':
            # Convert documentation to LaTeX prose
            converted = convert_markdown_to_latex(content)
            latex += converted + '\n\n'
        else:
            # Code block with syntax highlighting
            if content.strip():
                # Use minipage to prevent page breaks within code blocks
                latex += r'\begin{minipage}{\linewidth}' + '\n'
                latex += r'\begin{minted}{lean4}' + '\n'
                latex += content + '\n'
                latex += r'\end{minted}' + '\n'
                latex += r'\end{minipage}' + '\n\n'
    
    latex += r'\end{document}'
    return latex

def main():
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Convert a Lean 4 file with documentation comments to LaTeX with syntax highlighting.'
    )
    parser.add_argument('input_file', help='Path to the Lean file to convert')
    parser.add_argument('-o', '--output', help='Output directory (default: current directory)', default='.')
    parser.add_argument('-t', '--title', help='Document title (default: derived from filename)')
    parser.add_argument('--no-pdf', action='store_true', help='Generate LaTeX only, do not compile to PDF')
    
    args = parser.parse_args()
    
    input_path = Path(args.input_file)
    if not input_path.exists():
        print(f"Error: File not found: {args.input_file}")
        sys.exit(1)
    
    output_dir = Path(args.output)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    output_name = input_path.stem
    
    # Read input file
    with open(input_path, 'r') as f:
        content = f.read()
    
    # Parse into segments
    segments = parse_lean_file(content)
    
    # Generate LaTeX
    if args.title:
        title = args.title
    else:
        # Derive title from filename
        title = output_name.replace('_', ' ').title()
    
    latex = generate_latex(segments, title)
    
    # Write LaTeX file
    tex_file = output_dir / f"{output_name}.tex"
    with open(tex_file, 'w') as f:
        f.write(latex)
    
    print(f"Generated LaTeX file: {tex_file}")
    
    if args.no_pdf:
        print(f"Compile with: lualatex -shell-escape {output_name}.tex")
        return
    
    # Compile to PDF with LuaLaTeX
    print("Compiling to PDF with LuaLaTeX...")
    
    # Set environment variable for minted v3
    import os
    env = os.environ.copy()
    env['TEXMF_OUTPUT_DIRECTORY'] = str(output_dir.resolve())
    
    result = subprocess.run(
        ['lualatex', '-shell-escape', '-interaction=nonstopmode', f'{output_name}.tex'],
        cwd=str(output_dir),
        capture_output=True,
        env=env
    )
    
    if result.returncode != 0:
        print("First pass completed (may have warnings)")
    
    # Run again for references
    subprocess.run(
        ['lualatex', '-shell-escape', '-interaction=nonstopmode', f'{output_name}.tex'],
        cwd=str(output_dir),
        capture_output=True,
        env=env
    )
    
    pdf_file = output_dir / f"{output_name}.pdf"
    
    # Clean up intermediate files (do this regardless of success/failure)
    import shutil
    for ext in ['aux', 'log', 'out', 'toc', 'lof', 'lot', 'fls', 'fdb_latexmk']:
        intermediate = output_dir / f"{output_name}.{ext}"
        if intermediate.exists():
            intermediate.unlink()
    
    # Clean up minted cache files
    for minted_file in output_dir.glob('*.minted'):
        minted_file.unlink()
    
    # Clean up minted cache directory (primary target)
    minted_dir = output_dir / f"_minted-{output_name}"
    if minted_dir.exists() and minted_dir.is_dir():
        shutil.rmtree(minted_dir)
    
    # Clean up any other _minted-* directories (from previous runs)
    for minted_path in output_dir.glob('_minted-*'):
        if minted_path.is_dir():
            shutil.rmtree(minted_path)
    
    # Also check for plain "_minted" directory (some versions create this)
    plain_minted = output_dir / "_minted"
    if plain_minted.exists() and plain_minted.is_dir():
        shutil.rmtree(plain_minted)
    
    if pdf_file.exists():
        print(f"PDF created: {pdf_file}")
        print("Cleaned up intermediate files")
    else:
        print("PDF compilation failed. Check the LaTeX log file.")
        print("Cleaned up intermediate files")
        log_file = output_dir / f"{output_name}.log"
        if log_file.exists():
            with open(log_file, 'r', errors='ignore') as f:
                log_content = f.read()
                if '!' in log_content:
                    errors = [line for line in log_content.split('\n') if line.startswith('!')]
                    print("Errors found:")
                    for err in errors[:10]:
                        print(err)

if __name__ == "__main__":
    main()
if __name__ == "__main__":
    main()