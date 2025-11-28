# Publishing to GitHub - Step-by-Step Instructions

This guide walks you through publishing your Lewis Common Knowledge formalization to GitHub.

## Prerequisites

1. **GitHub account** - Create one at https://github.com if you don't have one
2. **Git installed** - Check with `git --version` in your terminal
3. **GitHub CLI (optional)** - Makes some steps easier: https://cli.github.com/

## Option 1: Using GitHub Web Interface (Easiest)

### Step 1: Create a New Repository

1. Go to https://github.com/new
2. Fill in:
   - **Repository name:** `lewis-common-knowledge-lean4`
   - **Description:** "Machine-verified formalizations of Lewis's theory of common knowledge in Lean 4"
   - **Visibility:** Public (recommended for academic work)
   - **DO NOT** initialize with README (we already have one)
3. Click "Create repository"

### Step 2: Upload Your Files

On your computer:

```bash
cd lewis-common-knowledge-lean4

# Initialize git repository
git init

# Add all files
git add .

# Create first commit
git commit -m "Initial commit: Complete formalization of Lewis's common knowledge theory"

# Add your GitHub repository as remote (replace YOUR_USERNAME)
git remote add origin https://github.com/YOUR_USERNAME/lewis-common-knowledge-lean4.git

# Push to GitHub
git branch -M main
git push -u origin main
```

### Step 3: Verify Upload

1. Go to your repository: `https://github.com/YOUR_USERNAME/lewis-common-knowledge-lean4`
2. Check that all files are there
3. Verify the README displays correctly

## Option 2: Using GitHub CLI (Faster)

```bash
cd lewis-common-knowledge-lean4

# Login to GitHub (first time only)
gh auth login

# Create repository and push in one command
gh repo create lewis-common-knowledge-lean4 --public --source=. --remote=origin --push

# That's it! Your repository is now live
```

## Post-Publication Steps

### 1. Add Topics/Tags

On your GitHub repository page:
1. Click the ⚙️ gear icon next to "About"
2. Add topics: `lean4`, `formal-verification`, `philosophy`, `game-theory`, `common-knowledge`, `justification-logic`
3. Add website: Link to your paper on Economics & Philosophy
4. Save changes

### 2. Enable GitHub Pages (Optional)

If you want to host the PDFs:
1. Go to Settings → Pages
2. Source: Deploy from a branch
3. Branch: main, folder: /pdfs
4. Save

### 3. Create a Release

```bash
# Tag the initial version
git tag -a v1.0.0 -m "Initial release: Complete formalization"
git push origin v1.0.0
```

Or on GitHub:
1. Go to "Releases" → "Create a new release"
2. Tag: `v1.0.0`
3. Title: "Initial Release - Complete Formalization"
4. Description: Link to your paper and describe the three approaches
5. Attach the PDFs (optional)
6. Publish release

### 4. Get a DOI via Zenodo (Recommended)

A DOI makes your formalization permanently citable in academic work.

#### Step-by-Step:

1. **Create a Zenodo account:**
   - Go to https://zenodo.org/
   - Sign in with your GitHub account

2. **Link your repository:**
   - Go to Settings → GitHub
   - Find `lewis-common-knowledge-lean4` in the list
   - Toggle the switch to ON

3. **Create a GitHub release:**
   - Follow step 3 above to create v1.0.0 release
   - Zenodo automatically detects new releases
   - Within minutes, Zenodo archives your release and assigns a DOI

4. **Get your DOI badge:**
   - Go to your Zenodo deposit page
   - Copy the DOI badge markdown
   - Replace `XXXXXXX` in README.md with your actual DOI number

5. **Update citations:**
   - Add DOI to your CV
   - Include DOI when citing your formalization
   - Update README.md with actual DOI link

Example: The badge in README.md will change from:
```markdown
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.XXXXXXX)
```
to:
```markdown
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.1234567.svg)](https://doi.org/10.5281/zenodo.1234567)
```

**Benefits:**
- ✅ Permanent archive (even if GitHub disappears)
- ✅ Formal citability in papers
- ✅ Counts as research output
- ✅ Indexed in academic databases
- ✅ Free for open-access research

### 5. Update Your Paper/CV

Add the GitHub link and DOI:
- In your CV: Include repository under "Software/Code"
- In future papers: Reference both GitHub and DOI
- On your website: Link to the repository

### 6. Announce Your Work

Consider announcing on:
- Twitter/X (academic community)
- Lean Zulip chat: https://leanprover.zulipchat.com/
- Philosophy forums/mailing lists
- Economics & Philosophy community

## Maintaining the Repository

### Accepting Contributions

When someone opens a pull request:

```bash
# Review the changes on GitHub first

# If you want to test locally:
git fetch origin pull/ID/head:BRANCH_NAME
git checkout BRANCH_NAME

# Test the changes
lake build

# If good, merge via GitHub interface or:
git checkout main
git merge BRANCH_NAME
git push origin main
```

### Updating Your Files

```bash
# Make changes to your files

# Stage changes
git add .

# Commit with descriptive message
git commit -m "Add semantics for justification logic"

# Push to GitHub
git push origin main
```

### Creating Branches for Experiments

```bash
# Create and switch to new branch
git checkout -b experimental-feature

# Make changes and commit
git add .
git commit -m "Experiment with probabilistic reasoning"

# Push branch to GitHub
git push origin experimental-feature

# Create pull request on GitHub to merge into main
```

## Troubleshooting

### "Permission denied" error

You need to set up authentication:

**Option A: HTTPS with token**
1. Generate personal access token: GitHub Settings → Developer settings → Personal access tokens
2. Use token as password when prompted

**Option B: SSH keys** (recommended)
```bash
# Generate SSH key
ssh-keygen -t ed25519 -C "your_email@example.com"

# Copy public key
cat ~/.ssh/id_ed25519.pub

# Add to GitHub: Settings → SSH and GPG keys → New SSH key

# Use SSH URL instead
git remote set-url origin git@github.com:YOUR_USERNAME/lewis-common-knowledge-lean4.git
```

### Large file error

The PDFs should be fine, but if you add very large files:

```bash
# Use Git LFS for files > 50MB
git lfs install
git lfs track "*.pdf"
git add .gitattributes
git commit -m "Track PDFs with Git LFS"
```

### Merge conflicts

```bash
# Pull latest changes
git pull origin main

# Fix conflicts in your editor
# Look for <<<<<<< markers

# After fixing:
git add .
git commit -m "Resolve merge conflicts"
git push origin main
```

## Best Practices

1. **Commit often** - Small, logical commits are better than large ones
2. **Write good commit messages** - Explain what and why, not just what
3. **Use branches** for experimental features
4. **Tag releases** when you publish papers referencing the code
5. **Respond to issues** - Even "I don't know" is better than silence
6. **Keep README updated** - It's the first thing people see

## Example Commit Messages

Good:
```
✓ "Add counterexample for C4 in Sillari approach"
✓ "Prove A6 in justification logic (closes #12)"
✓ "Refactor R-closure definition for clarity"
✓ "Update README with installation instructions"
```

Less good:
```
✗ "Update file"
✗ "Fix"
✗ "Changes"
✗ "asdf"
```

## Citation Template for Your Repository

Once published, update the README.md with the actual URL:

```bibtex
@software{vromen2024lean,
  title={Formalizing Lewis's Theory of Common Knowledge in Lean 4},
  author={Vromen, Huub},
  year={2024},
  url={https://github.com/YOUR_USERNAME/lewis-common-knowledge-lean4},
  note={Machine-verified formalizations accompanying Vromen (2024)}
}
```

## Getting Help

- **GitHub Docs:** https://docs.github.com/
- **Lean Zulip:** https://leanprover.zulipchat.com/
- **Git Book:** https://git-scm.com/book/en/v2

## Checklist Before Publishing

- [ ] All files are in the correct directories
- [ ] README.md has your actual GitHub username (not "yourusername")
- [ ] LICENSE file is present
- [ ] .gitignore is configured for Lean projects
- [ ] All Lean files compile (`lake build` succeeds)
- [ ] No `sorry` statements (or clearly marked as future work)
- [ ] PDFs are included and readable
- [ ] Email address in README is correct
- [ ] Citation information is accurate

---

Once you've published, your formalization will be:
- ✅ Permanently accessible
- ✅ Citable in papers
- ✅ Open for contributions
- ✅ Part of the formal methods community
- ✅ A resource for future research

Good luck with your publication! 🚀
