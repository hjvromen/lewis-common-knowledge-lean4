#!/bin/bash
# Quick setup script for the Lewis Common Knowledge formalization project

set -e

echo "=========================================="
echo "Lewis Common Knowledge - Setup Script"
echo "=========================================="
echo ""

# Check if elan is installed
if ! command -v elan &> /dev/null; then
    echo "⚠️  elan (Lean version manager) not found"
    echo "Installing elan..."
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
    export PATH="$HOME/.elan/bin:$PATH"
    echo "✓ elan installed"
else
    echo "✓ elan found"
fi

# Check Lean version
echo ""
echo "Checking Lean version..."
lean --version

# Update Lake dependencies
echo ""
echo "Updating Lake dependencies (this may take a while)..."
lake update

# Build the project
echo ""
echo "Building project..."
lake build

# Check for sorry statements
echo ""
echo "Verifying proof completeness..."
if grep -r "sorry" src/*.lean; then
    echo "⚠️  WARNING: Found 'sorry' statements in source files"
    echo "   Some proofs are incomplete"
else
    echo "✓ All proofs complete - no 'sorry' statements found!"
fi

echo ""
echo "=========================================="
echo "Setup complete! 🎉"
echo "=========================================="
echo ""
echo "Next steps:"
echo "  1. Open in VS Code: code ."
echo "  2. Read the README: cat README.md"
echo "  3. Start with: pdfs/cubitt_sugden_baseline.pdf"
echo "  4. Explore: src/*.lean files"
echo ""
echo "Happy formalizing!"
