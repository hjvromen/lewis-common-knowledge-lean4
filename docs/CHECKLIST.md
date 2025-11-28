# Pre-Publication Checklist

Use this checklist before publishing your formalization to GitHub.

## ✅ Files and Structure

- [x] All Lean files in `src/` directory
- [x] All PDFs in `pdfs/` directory
- [x] README.md present and complete
- [x] LICENSE file present (MIT)
- [x] .gitignore configured for Lean
- [x] lakefile.lean present
- [x] lean-toolchain specifies version
- [x] CONTRIBUTING.md present
- [x] Documentation in `docs/` directory

## ✅ Content Verification

### Lean Files
- [x] Sillari_refutation.lean compiles
- [x] Cubitt_Sugden_baseline.lean compiles
- [x] Vromen_justification_logic.lean compiles
- [x] No `sorry` statements (or clearly marked)
- [x] All imports resolve correctly
- [x] Comments and documentation present

### Documentation
- [x] README has accurate description
- [x] README has correct file structure
- [x] README has installation instructions
- [x] README has citation information
- [x] Author email is correct
- [x] References are complete

## ⚠️ Things to Update Before Publishing

### Replace Placeholders

In `README.md`:
- [ ] Change `yourusername` to your actual GitHub username
- [ ] Update repository URL throughout
- [ ] Verify email address is what you want public

In this checklist:
- [ ] Update the repository URL in citation examples

### Personalization

- [ ] Add any acknowledgments specific to your institution
- [ ] Update author bio if desired
- [ ] Add links to your personal website/ORCID if applicable

## 🧪 Testing

### Local Build
```bash
cd lewis-common-knowledge-lean4
lake update
lake build
```

- [ ] `lake update` completes successfully
- [ ] `lake build` completes without errors
- [ ] No deprecation warnings

### Content Review
- [ ] All PDFs open and display correctly
- [ ] Paper PDF is the final published version
- [ ] Lean files have sensible names
- [ ] Directory structure is logical

## 📝 Documentation Quality

- [ ] README is clear and informative
- [ ] GUIDE.md helps newcomers navigate
- [ ] Code comments explain non-obvious parts
- [ ] Examples are provided where helpful
- [ ] Mathematical notation is consistent

## 🌐 GitHub Preparation

### Repository Settings
- [ ] Repository name: `lewis-common-knowledge-lean4`
- [ ] Description: One-line summary
- [ ] Visibility: Public (recommended)
- [ ] Don't initialize with README (we have one)

### Initial Commit
```bash
git init
git add .
git commit -m "Initial commit: Complete formalization of Lewis's common knowledge"
```

- [ ] Git initialized
- [ ] All files staged
- [ ] Meaningful commit message

## 🚀 Post-Publication

### Immediately After
- [ ] Verify all files uploaded correctly
- [ ] Check README renders properly on GitHub
- [ ] Test clone and build from fresh checkout

### Within 24 Hours
- [ ] Add topics/tags to repository
- [ ] Create initial release (v1.0.0)
- [ ] Update CV with repository link
- [ ] Share on social media/academic networks

### Within One Week
- [ ] Consider writing blog post about the formalization
- [ ] Post to Lean Zulip chat
- [ ] Email interested colleagues
- [ ] Update personal website

## 📊 Metrics to Track

After publication, monitor:
- [ ] GitHub stars (indicates interest)
- [ ] Issues opened (shows engagement)
- [ ] Forks (others building on your work)
- [ ] Citations (academic impact)

## 🛠️ Maintenance Plan

### Regular Tasks
- [ ] Respond to issues within 1 week
- [ ] Review pull requests when submitted
- [ ] Update dependencies periodically
- [ ] Fix any breaking changes from Lean updates

### Optional Enhancements
- [ ] Add more examples
- [ ] Create tutorial notebooks
- [ ] Record video walkthrough
- [ ] Write follow-up papers

## ⚡ Quick Pre-Publish Commands

Run these right before publishing:

```bash
# Verify no sorry statements
grep -r "sorry" src/*.lean && echo "Found sorry!" || echo "Clean!"

# Check all files present
ls -R | grep -E "\.lean$|\.md$|\.pdf$"

# Verify build
lake build

# Count lines of code
find src -name "*.lean" -exec wc -l {} + | tail -1

# Initialize git (if not done)
git init
git add .
git status
```

## 🎯 Quality Checklist

Rate each aspect (1-5 stars):

**Code Quality**
- [ ] ⭐⭐⭐⭐⭐ All proofs complete
- [ ] ⭐⭐⭐⭐⭐ Well-documented
- [ ] ⭐⭐⭐⭐⭐ Consistent style
- [ ] ⭐⭐⭐⭐⭐ Builds without errors

**Documentation**
- [ ] ⭐⭐⭐⭐⭐ README is comprehensive
- [ ] ⭐⭐⭐⭐⭐ Clear usage instructions
- [ ] ⭐⭐⭐⭐⭐ Mathematical content explained
- [ ] ⭐⭐⭐⭐⭐ References are complete

**Reproducibility**
- [ ] ⭐⭐⭐⭐⭐ Setup instructions clear
- [ ] ⭐⭐⭐⭐⭐ Dependencies specified
- [ ] ⭐⭐⭐⭐⭐ Version locked
- [ ] ⭐⭐⭐⭐⭐ CI/CD configured

## 🚨 Common Mistakes to Avoid

- [ ] ❌ Forgetting to replace "yourusername" in URLs
- [ ] ❌ Including personal files (.DS_Store, etc.)
- [ ] ❌ Committing build artifacts (.lake/, build/)
- [ ] ❌ Using absolute paths in documentation
- [ ] ❌ Forgetting to test fresh clone
- [ ] ❌ Not checking PDF file sizes (GitHub limits)
- [ ] ❌ Including private email addresses you don't want public
- [ ] ❌ Copying .git folder from another project

## 📋 Final Sanity Checks

**Before running `git push`:**

1. [ ] Review `git status` - everything staged?
2. [ ] Review `git diff --staged` - changes look right?
3. [ ] Commit message is descriptive?
4. [ ] GitHub remote URL is correct?
5. [ ] You're pushing to the right branch?

**After publishing:**

1. [ ] Visit repository URL - does it load?
2. [ ] Click through files - do they display?
3. [ ] Try cloning fresh - does it build?
4. [ ] README renders correctly?
5. [ ] PDFs are accessible?

## ✨ Bonus: Make it Shine

### GitHub Profile README
Add to your profile:
```markdown
## 🔬 Research Software

- [Lewis Common Knowledge Formalization](https://github.com/yourusername/lewis-common-knowledge-lean4) - 
  Machine-verified proofs of Lewis's common knowledge theory in Lean 4
```

### Academic CV
Add to publications/software:
```latex
\item Vromen, H. (2024). 
\textit{Formalizing Lewis's Theory of Common Knowledge in Lean 4}.
\url{https://github.com/yourusername/lewis-common-knowledge-lean4}
```

### Social Media Announcement
```
🎉 Just published my Lean 4 formalization of David Lewis's 
common knowledge theory!

✅ All proofs machine-verified
🔬 Three different approaches compared
📚 Extensively documented

Check it out: [URL]

Paper: Vromen (2024) Economics & Philosophy

#Lean4 #FormalVerification #Philosophy
```

## 🎓 Remember

This formalization represents months of work. Take time to:
- ✅ Get it right before publishing
- ✅ Document thoroughly for others
- ✅ Test everything works
- ✅ Celebrate your achievement!

---

**Once all boxes are checked, you're ready to publish!** 

See `PUBLISHING.md` for detailed instructions.

Good luck! 🚀
