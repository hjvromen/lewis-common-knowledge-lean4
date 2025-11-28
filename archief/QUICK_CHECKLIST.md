# Quick Reference Checklist: Publishing Lewis to GitHub

Use this as a quick reference while following the detailed guide.

## Pre-Publishing Checklist

### Local Preparation
- [ ] Clean up directory (remove .DS_Store, __MACOSX)
- [ ] Create/update .gitignore
- [ ] Write comprehensive README.md
- [ ] Create CITATION.cff
- [ ] Create CONTRIBUTING.md
- [ ] Create LICENSE (MIT recommended)
- [ ] Add your academic paper to papers/ directory
- [ ] Test that project builds: `lake build`
- [ ] Verify all Lean files compile

### Git Setup
- [ ] Initialize git repository: `git init`
- [ ] Stage all files: `git add .`
- [ ] Create initial commit with descriptive message
- [ ] Verify commit: `git log`

## GitHub Publishing

### Create Repository
- [ ] Log in to GitHub
- [ ] Create new repository named "Lewis"
- [ ] Set as Public
- [ ] Do NOT initialize with README/license (you have these)
- [ ] Copy repository URL

### Push to GitHub
```bash
git remote add origin https://github.com/YOUR-USERNAME/Lewis.git
git branch -M main
git push -u origin main
```

- [ ] Verify files uploaded correctly
- [ ] Check README displays properly

## Configuration

### Repository Settings
- [ ] Add description in About section
- [ ] Add topics/tags: lean4, formal-verification, philosophy, epistemology, etc.
- [ ] Add website link (to paper or your academic page)
- [ ] Enable Issues in Settings
- [ ] Enable Discussions (optional)

### Documentation
- [ ] Update README with correct GitHub username
- [ ] Add badges (Lean 4, License, DOI)
- [ ] Verify all links work
- [ ] Add ORCID if you have one

### First Release
- [ ] Go to Releases → Create new release
- [ ] Tag: v1.0.0
- [ ] Title: "Initial Release: Lewis Common Knowledge Formalization v1.0.0"
- [ ] Write release notes
- [ ] Attach paper PDF
- [ ] Publish release

## Post-Publishing

### Verification
- [ ] Clone repository in fresh directory
- [ ] Run `lake build` to verify it works
- [ ] Check all documentation links
- [ ] Test that files download correctly

### Sharing
- [ ] Share on Lean Zulip
- [ ] Tweet/post about it (use #Lean4 #FormalVerification)
- [ ] Update your CV/academic profiles
- [ ] Add GitHub link to paper acknowledgments
- [ ] Inform your department/supervisor

### Maintenance Setup
- [ ] Set up email notifications for issues
- [ ] Star your own repo (for visibility)
- [ ] Watch your repo for activity
- [ ] Prepare to respond to first issues/questions

## Optional Enhancements

### Enhanced Visibility
- [ ] Get Zenodo DOI for code citability
- [ ] Set up GitHub Pages
- [ ] Create video/blog post explaining the work
- [ ] Submit to Lean community showcase
- [ ] Add to relevant "awesome" lists

### Integration
- [ ] Link from paper to GitHub
- [ ] Link from GitHub to paper
- [ ] Cross-reference with related projects
- [ ] Consider adding to Lean mathlib if applicable

## Quick Commands Reference

### Essential Git Commands
```bash
# Check status
git status

# Add files
git add .

# Commit changes
git commit -m "Your message"

# Push to GitHub
git push origin main

# Pull updates
git pull origin main

# Check remote
git remote -v

# View commit history
git log --oneline
```

### Essential Lake Commands
```bash
# Build project
lake build

# Update dependencies
lake update

# Clean build
lake clean

# Check specific file
lake env lean Lewis/Cubitt_Sugden_baseline.lean
```

## Common Issues & Quick Fixes

| Problem | Quick Fix |
|---------|-----------|
| Authentication fails | Use Personal Access Token instead of password |
| Large files won't push | Add to .gitignore or use Git LFS |
| Build fails on clone | Check lean-toolchain version, run lake update |
| .DS_Store appears | Add to .gitignore, run `find . -name ".DS_Store" -delete` |
| Wrong branch name | `git branch -M main` |

## File Structure Quick Reference

```
Lewis/
├── .git/                 # Git repository (don't touch)
├── .gitignore           # Files to ignore
├── README.md            # Main project documentation
├── LICENSE              # MIT License
├── CITATION.cff         # Citation metadata
├── CONTRIBUTING.md      # Contribution guidelines
├── Lewis.lean           # Main entry point
├── lakefile.lean        # Build configuration
├── lean-toolchain       # Lean version
├── Lewis/               # Main formalization files
│   ├── Cubitt_Sugden_baseline.lean
│   ├── Sillari_refutation.lean
│   ├── Vromen_justification_logic.lean
│   └── *.pdf, *.tex     # Documentation
├── papers/              # Academic paper
│   └── Vromen_2024.pdf
├── docs/                # Additional documentation
└── archief/             # Archive/historical materials
```

## Timeline Estimate

- **Preparation**: 1-2 hours
- **GitHub setup**: 30 minutes
- **Documentation**: 1-2 hours
- **Testing**: 30 minutes
- **Announcement**: 30 minutes

**Total**: 4-6 hours for complete professional setup

## Support

- Lean Zulip: https://leanprover.zulipchat.com
- GitHub Docs: https://docs.github.com
- Git Tutorial: https://git-scm.com/docs/gittutorial

## Notes

- Keep your GitHub username consistent with academic profiles
- Respond to issues within 48 hours when possible
- Update README if project structure changes
- Create new releases for significant updates
- Back up your work regularly

---

**Remember**: Publishing is just the beginning. The real value comes from engagement with the community!
