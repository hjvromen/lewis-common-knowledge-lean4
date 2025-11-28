# GitHub Publishing Guide for Lewis Common Knowledge Formalization

This guide provides step-by-step instructions for publishing your Lean 4 formalization of David Lewis's theory of common knowledge to GitHub.

## Project Overview

**Project Name**: Lewis Common Knowledge Formalization in Lean 4  
**Based on**: Vromen, H. (2024). "Reasoning with reasons: Lewis on common knowledge." *Economics & Philosophy*, 40, 397-418.

**Description**: Formal verification of David Lewis's convention theory, featuring three distinct approaches:
1. Cubitt-Sugden baseline formalization
2. Sillari's modal logic critique (with refutation)
3. Vromen's justification logic solution

## Prerequisites

Before you begin, ensure you have:
- [ ] A GitHub account (create one at https://github.com if needed)
- [ ] Git installed on your computer
- [ ] Access to your Lewis project directory
- [ ] Your academic paper (Vromen 2024) as PDF

## Step-by-Step Publishing Process

### Step 1: Prepare Your Repository Locally

Your project already has a Git repository initialized (there's a `.git` folder in `Lewis/Lewis/`), but we need to clean it up and reorganize it for publication.

#### 1.1 Clean Up the Directory Structure

```bash
# Navigate to your project root
cd /path/to/Lewis

# Remove macOS system files
find . -name ".DS_Store" -delete
find . -name "__MACOSX" -type d -exec rm -rf {} + 2>/dev/null || true

# Remove the nested .git if it exists (we'll use the top-level one)
rm -rf Lewis/.git

# Initialize git at the top level if not already done
git init
```

#### 1.2 Create a Proper .gitignore

Create or update `.gitignore` in your project root:

```gitignore
# Lean build artifacts
/.lake/
/build/
*.olean
*.olean.trace
*.ilean
*.ilean.trace

# macOS
.DS_Store
__MACOSX/

# Editor files
.vscode/
*.swp
*.swo
*~

# LaTeX auxiliary files
*.aux
*.log
*.out
*.toc
*.synctex.gz
*.fdb_latexmk
*.fls
*.bbl
*.blg

# Python
__pycache__/
*.pyc
*.pyo

# Temporary files
*.tmp
*.bak
```

### Step 2: Create Essential Documentation Files

#### 2.1 Create a Comprehensive README.md

Create `README.md` in your project root:

```markdown
# Formal Verification of Lewis's Common Knowledge Theory

[![Lean 4](https://img.shields.io/badge/Lean-4-blue)](https://leanprover.github.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

This repository contains a formal verification in Lean 4 of David Lewis's account of common knowledge from his theory of conventions, as developed in:

**Vromen, H. (2024)**. "Reasoning with reasons: Lewis on common knowledge." *Economics & Philosophy*, 40, 397-418. [DOI: 10.1017/S0266267123000238](https://doi.org/10.1017/S0266267123000238)

## Overview

David Lewis introduced the concept of common knowledge in his seminal 1969 work on conventions. Unlike later accounts in philosophy and economics that focus on knowledge states, Lewis's theory centers on **reasons to believe** rather than psychological states. This formalization project implements and verifies three different approaches:

1. **Cubitt-Sugden Baseline** (`Cubitt_Sugden_baseline.lean`) - The foundational formalization following Cubitt & Sugden's (2003) interpretation
2. **Sillari's Modal Logic** (`Sillari_refutation.lean`) - An analysis of Sillari's (2005) modal logic approach, including identification of key inconsistencies
3. **Vromen's Justification Logic** (`Vromen_justification_logic.lean`) - A novel formalization using justification logic that resolves gaps in Lewis's original argument

## Key Contributions

- **Complete formal verification** of Lewis's theorem that a basis for common knowledge generates an infinite chain of higher-order reasons to believe
- **Identification of inconsistencies** in Sillari's (2005) proposed formalization
- **Novel approach** using justification logic to represent reasons as first-class objects
- **Machine-checked proofs** ensuring mathematical rigor

## Structure

```
Lewis/
├── Lewis/
│   ├── Cubitt_Sugden_baseline.lean     # Baseline formalization
│   ├── Sillari_refutation.lean         # Modal logic critique
│   ├── Vromen_justification_logic.lean # Justification logic approach
│   ├── *.pdf                            # Generated documentation
│   ├── *.tex                            # LaTeX sources
│   └── lean_to_latex.py                 # Extraction tool
├── docs/                                # Additional documentation
├── archief/                             # Archive materials
├── Lewis.lean                           # Main entry point
├── lakefile.lean                        # Lake build configuration
└── lean-toolchain                       # Lean version specification
```

## Building the Project

### Prerequisites

- [Lean 4](https://leanprover.github.io/) (version specified in `lean-toolchain`)
- [Lake](https://github.com/leanprover/lake) (Lean's build tool)

### Build Instructions

```bash
# Clone the repository
git clone https://github.com/YOUR-USERNAME/Lewis.git
cd Lewis

# Build the project
lake build

# Check all proofs
lake exe lean Lewis/Cubitt_Sugden_baseline.lean
lake exe lean Lewis/Sillari_refutation.lean
lake exe lean Lewis/Vromen_justification_logic.lean
```

## Key Definitions and Theorems

### Reason to Believe

In our justification logic approach, `r :ᵢ φ` represents "r is a reason for agent i to believe φ". This treats reasons as explicit objects that can be reasoned about, rather than as modal operators.

### Indication

Lewis's concept of indication is formalized as: `Indᵢ A φ` means "i has a reason to believe that A implies φ".

### Lewis's Theorem

The main result: If a state of affairs A is a basis for common knowledge of proposition φ in group P, then all finitely nested formulas `Rᵢ Rⱼ ... Rₖ φ` hold for all agents i, j, ..., k in P.

## Documentation

Each `.lean` file has a corresponding `.pdf` document with detailed explanations:

- `Cubitt_sugden_baseline.pdf` - Baseline formalization documentation
- `sillari_refutation.pdf` - Modal logic critique
- `vromen_justification_logic.pdf` - Justification logic approach

These are generated automatically using `lean_to_latex.py`.

## Academic Context

This formalization is part of ongoing research on:
- Formal verification of philosophical arguments
- Applications of justification logic to epistemic concepts
- The foundations of coordination theory and common knowledge

Related publications:
- Lewis, D. (1969). *Convention: A Philosophical Study*. Harvard University Press.
- Cubitt, R. P., & Sugden, R. (2003). "Common knowledge, salience and convention: a reconstruction of David Lewis' game theory." *Economics and Philosophy*, 19, 175-210.
- Sillari, G. (2005). "A logical framework for convention." *Synthese*, 147, 379-400.

## Citation

If you use this formalization in your research, please cite:

```bibtex
@article{vromen2024reasoning,
  title={Reasoning with reasons: Lewis on common knowledge},
  author={Vromen, Huub},
  journal={Economics \& Philosophy},
  volume={40},
  pages={397--418},
  year={2024},
  publisher={Cambridge University Press},
  doi={10.1017/S0266267123000238}
}
```

## Author

**Huub Vromen**  
Radboud University, Department of Philosophy  
Email: hjvromen@icloud.com

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Acknowledgments

Thanks to the Lean community for their support, and to the reviewers and editors at *Economics & Philosophy* for their valuable feedback.

## Contributing

Contributions, issues, and feature requests are welcome! Feel free to check the [issues page](https://github.com/YOUR-USERNAME/Lewis/issues).

## Future Work

- Extension to other epistemic operators
- Application to game-theoretic coordination problems
- Integration with existing Lean libraries for modal and epistemic logic
- Formalization of the transition from reasons to believe to actual beliefs
```

#### 2.2 Create CITATION.cff

Create `CITATION.cff` for proper academic citation:

```yaml
cff-version: 1.2.0
message: "If you use this software, please cite both the software and the paper."
title: "Formal Verification of Lewis's Common Knowledge Theory"
authors:
  - family-names: "Vromen"
    given-names: "Huub"
    email: "hjvromen@icloud.com"
    affiliation: "Radboud University, Department of Philosophy"
    orcid: "https://orcid.org/YOUR-ORCID-HERE"
repository-code: "https://github.com/YOUR-USERNAME/Lewis"
license: MIT
preferred-citation:
  type: article
  authors:
    - family-names: "Vromen"
      given-names: "Huub"
  title: "Reasoning with reasons: Lewis on common knowledge"
  journal: "Economics & Philosophy"
  volume: 40
  start: 397
  end: 418
  year: 2024
  doi: "10.1017/S0266267123000238"
```

#### 2.3 Create CONTRIBUTING.md

```markdown
# Contributing to Lewis Common Knowledge Formalization

Thank you for your interest in contributing to this project!

## How to Contribute

### Reporting Issues

If you find a bug or have a suggestion:

1. Check if the issue already exists
2. If not, create a new issue with:
   - Clear description of the problem or suggestion
   - Steps to reproduce (for bugs)
   - Expected vs. actual behavior
   - Lean version and environment details

### Submitting Changes

1. Fork the repository
2. Create a new branch for your feature/fix
3. Make your changes
4. Ensure all proofs still compile
5. Update documentation as needed
6. Submit a pull request

### Code Style

- Follow Lean 4 naming conventions
- Add comments for non-obvious proofs
- Include docstrings for major definitions and theorems
- Keep lines under 100 characters where possible

### Testing

Before submitting:

```bash
lake build
lake exe lean Lewis/Cubitt_Sugden_baseline.lean
lake exe lean Lewis/Sillari_refutation.lean
lake exe lean Lewis/Vromen_justification_logic.lean
```

## Questions?

Feel free to open an issue for questions or discussion.
```

### Step 3: Organize Your Files

#### 3.1 Add Your Academic Paper

```bash
# Create a papers directory
mkdir -p papers

# Copy your paper (adjust path as needed)
cp /path/to/Vromen_-_2024_-_Reasoning_with_reasons_Lewis_on_common_knowledge.pdf papers/
```

#### 3.2 Clean Up Documentation

Organize your documentation in the `docs/` folder:

```bash
# Your docs are already in docs/, just ensure they're organized
# Consider adding a docs/README.md to explain the documentation structure
```

### Step 4: Initialize and Commit Your Repository

```bash
# Make sure you're in the project root
cd /path/to/Lewis

# Initialize git if not already done
git init

# Add all files
git add .

# Create initial commit
git commit -m "Initial commit: Lean 4 formalization of Lewis's common knowledge theory

This formalization verifies David Lewis's account of common knowledge from his
convention theory, implementing three approaches:
- Cubitt-Sugden baseline formalization
- Sillari modal logic critique with refutation
- Novel justification logic solution

Based on: Vromen, H. (2024). Reasoning with reasons: Lewis on common knowledge.
Economics & Philosophy, 40, 397-418."
```

### Step 5: Create GitHub Repository

#### 5.1 On GitHub Website

1. Go to https://github.com
2. Click the "+" icon in the top right
3. Select "New repository"
4. Fill in the details:
   - **Repository name**: `Lewis`
   - **Description**: "Formal verification in Lean 4 of David Lewis's common knowledge theory from convention theory"
   - **Visibility**: Public (recommended for academic work)
   - **DO NOT** initialize with README, .gitignore, or license (we already have these)
5. Click "Create repository"

#### 5.2 Link Local Repository to GitHub

```bash
# Add GitHub as remote origin (replace YOUR-USERNAME)
git remote add origin https://github.com/YOUR-USERNAME/Lewis.git

# Verify remote was added
git remote -v

# Push to GitHub
git branch -M main
git push -u origin main
```

### Step 6: Configure Repository Settings

On GitHub, go to your repository settings:

#### 6.1 About Section

1. Click the gear icon next to "About"
2. Add:
   - Description: "Formal verification in Lean 4 of David Lewis's common knowledge theory"
   - Website: Link to your academic page or the published paper
   - Topics: `lean4`, `formal-verification`, `epistemology`, `common-knowledge`, `philosophy`, `justification-logic`, `modal-logic`

#### 6.2 Enable Issues

1. Settings → General → Features
2. Ensure "Issues" is checked

#### 6.3 Add Repository Details

In the README.md, update:
- Replace `YOUR-USERNAME` with your actual GitHub username
- Add your ORCID if you have one
- Add links to related work

### Step 7: Create Releases

Create a release for your formalization:

1. Go to "Releases" on your repository page
2. Click "Create a new release"
3. Tag version: `v1.0.0`
4. Release title: "Initial Release: Lewis Common Knowledge Formalization v1.0.0"
5. Description:

```markdown
## Lewis Common Knowledge Formalization v1.0.0

First public release of the Lean 4 formalization of David Lewis's theory of common knowledge.

### Features

- Complete formalization of Cubitt-Sugden baseline approach
- Sillari modal logic critique with identified inconsistencies
- Novel justification logic solution resolving Lewis's argument gaps
- Machine-checked proofs of Lewis's theorem
- Comprehensive documentation with auto-generated LaTeX

### Academic Paper

This formalization accompanies:

Vromen, H. (2024). "Reasoning with reasons: Lewis on common knowledge." 
*Economics & Philosophy*, 40, 397-418. 
DOI: [10.1017/S0266267123000238](https://doi.org/10.1017/S0266267123000238)

### Lean Version

Requires Lean 4 (see `lean-toolchain` for exact version)

### Installation

```bash
git clone https://github.com/YOUR-USERNAME/Lewis.git
cd Lewis
lake build
```
```

6. Attach your paper PDF as a release asset
7. Publish release

### Step 8: Add Documentation Features

#### 8.1 Create GitHub Pages (Optional)

If you want a project website:

1. Settings → Pages
2. Source: "Deploy from a branch"
3. Branch: `main` / `/docs`
4. Save

Create `docs/index.md` with project overview.

#### 8.2 Add Badges to README

Update your README with useful badges:

```markdown
[![Lean 4](https://img.shields.io/badge/Lean-4-blue)](https://leanprover.github.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![DOI](https://img.shields.io/badge/DOI-10.1017%2FS0266267123000238-blue)](https://doi.org/10.1017/S0266267123000238)
[![GitHub release](https://img.shields.io/github/release/YOUR-USERNAME/Lewis.svg)](https://github.com/YOUR-USERNAME/Lewis/releases)
```

### Step 9: Share Your Work

After publishing, announce your formalization:

1. **Social Media**: Share on Twitter/X with hashtags #Lean4 #FormalVerification #Philosophy
2. **Lean Zulip**: Post in the "new members" or "mathlib" streams at https://leanprover.zulipchat.com
3. **Academic Networks**: Update your ResearchGate, Academia.edu, or similar profiles
4. **Department**: Share with your department at Radboud University
5. **Journals**: Consider mentioning in follow-up papers or as supplementary material

### Step 10: Maintain Your Repository

#### Regular Updates

```bash
# Pull latest changes
git pull origin main

# Make changes to files
# ...

# Commit changes
git add .
git commit -m "Description of changes"

# Push to GitHub
git push origin main
```

#### Respond to Issues

- Check GitHub regularly for issues or questions
- Provide helpful responses
- Label issues appropriately
- Close resolved issues

## Post-Publication Checklist

After publishing to GitHub:

- [ ] Verify all files are present and correctly organized
- [ ] Check that README.md displays correctly
- [ ] Test clone and build instructions work
- [ ] Add GitHub link to your CV and academic profiles
- [ ] Update paper/CV to mention "Code available at: [GitHub link]"
- [ ] Share on relevant platforms (Lean Zulip, Twitter, academic networks)
- [ ] Add DOI badge linking to published paper
- [ ] Consider archiving to Zenodo for a citable DOI for the code
- [ ] Respond to any initial issues or questions

## Advanced: Getting a DOI for Your Code

For maximum citability, get a DOI from Zenodo:

1. Go to https://zenodo.org
2. Sign in with your GitHub account
3. Go to Settings → GitHub
4. Enable the Lewis repository
5. Create a new release on GitHub
6. Zenodo will automatically create a DOI
7. Add the DOI badge to your README

## Troubleshooting

### Common Issues

**Problem**: `git push` fails with authentication error
- **Solution**: Set up SSH keys or use Personal Access Token (PAT) instead of password

**Problem**: Large files failing to push
- **Solution**: Use Git LFS for large PDFs or binary files

**Problem**: Build fails on fresh clone
- **Solution**: Ensure `lean-toolchain` specifies correct Lean version, run `lake update`

## Additional Resources

- [GitHub Documentation](https://docs.github.com)
- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Git Tutorial](https://git-scm.com/docs/gittutorial)
- [Lean Zulip Chat](https://leanprover.zulipchat.com)

## Questions?

If you have questions about this guide or the publishing process, feel free to reach out or open an issue in the repository.

---

*This guide is tailored for the Lewis Common Knowledge Formalization project by Huub Vromen, Radboud University.*
