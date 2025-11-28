# Getting a DOI for Your Formalization

A Digital Object Identifier (DOI) makes your formalization permanently citable and archived. This guide walks you through the process.

## Why Get a DOI?

### Academic Benefits
- ✅ **Permanent citation** - Unlike GitHub URLs, DOIs never change
- ✅ **Academic credit** - Recognized as a formal research output
- ✅ **Discoverability** - Indexed in academic databases
- ✅ **CV enhancement** - Counts as a citable publication
- ✅ **Version tracking** - Each release gets its own DOI

### Practical Benefits
- ✅ **Free** - No cost for open-access research
- ✅ **Automatic** - Integrates with GitHub releases
- ✅ **Reliable** - CERN-backed archival system
- ✅ **Standard practice** - Expected in formal methods community

## Step-by-Step Guide

### Step 1: Publish to GitHub First

Make sure your repository is on GitHub (follow PUBLISHING.md):
```bash
git remote -v
# Should show: origin https://github.com/yourusername/lewis-common-knowledge-lean4.git
```

### Step 2: Create Zenodo Account

1. Go to https://zenodo.org/
2. Click "Sign up" or "Log in"
3. Choose "Log in with GitHub"
4. Authorize Zenodo to access your GitHub account
5. Complete your Zenodo profile (optional but recommended)

### Step 3: Link Your Repository to Zenodo

1. Once logged into Zenodo, go to: https://zenodo.org/account/settings/github/
2. You'll see a list of your GitHub repositories
3. Find `lewis-common-knowledge-lean4`
4. **Toggle the switch to ON** (this is the key step!)
5. The repository is now linked

**Note:** If you don't see your repository:
- Make sure you're logged in with the correct GitHub account
- Refresh the page
- Check that the repository is public (not private)
- Wait a few minutes and try again

### Step 4: Create Your First Release on GitHub

This triggers Zenodo to archive your code and assign a DOI.

**Option A: Via GitHub Web Interface**

1. Go to your repository: `https://github.com/yourusername/lewis-common-knowledge-lean4`
2. Click "Releases" (right sidebar)
3. Click "Create a new release"
4. Fill in:
   - **Tag version:** `v1.0.0`
   - **Release title:** `v1.0.0 - Initial Complete Formalization`
   - **Description:**
     ```markdown
     This is the first complete release of the Lewis Common Knowledge formalization in Lean 4.
     
     ## Features
     - Complete machine-verified proofs of all three approaches
     - Sillari refutation with counterexamples
     - Cubitt-Sugden baseline formalization
     - Vromen justification logic solution
     - Comprehensive documentation and PDFs
     
     ## Citation
     Accompanies: Vromen, H. (2024). Reasoning with reasons: Lewis on common knowledge. 
     Economics & Philosophy, 40(2), 397–418. DOI: 10.1017/S0266267123000238
     
     All proofs verified with Lean 4.13.0 and Mathlib.
     ```
5. Click "Publish release"

**Option B: Via Command Line**

```bash
# Create and push the tag
git tag -a v1.0.0 -m "Initial release: Complete formalization of Lewis's common knowledge"
git push origin v1.0.0

# Then create the release on GitHub web interface using the tag
```

### Step 5: Zenodo Automatically Creates DOI

Within a few minutes:

1. Zenodo detects your new GitHub release
2. Archives a copy of your repository
3. Assigns a permanent DOI
4. Creates a Zenodo deposit page

You'll receive an email notification when it's ready.

### Step 6: Get Your DOI and Update README

1. **Find your DOI:**
   - Go to https://zenodo.org/
   - Click "Upload" → "My uploads"
   - Find your deposit
   - Your DOI will look like: `10.5281/zenodo.1234567`

2. **Copy the badge code:**
   - On your Zenodo deposit page, scroll down
   - Click the "DOI" badge
   - Copy the markdown code

3. **Update README.md:**

Replace this line in your README:
```markdown
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.XXXXXXX)
```

With your actual DOI:
```markdown
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.1234567.svg)](https://doi.org/10.5281/zenodo.1234567)
```

4. **Update the software citation:**

Replace:
```bibtex
@software{vromen2024lean,
  title={Formalizing Lewis's Theory of Common Knowledge in Lean 4},
  author={Vromen, Huub},
  year={2024},
  doi={10.5281/zenodo.XXXXXXX},
  url={https://github.com/yourusername/lewis-common-knowledge-lean4},
  note={Replace XXXXXXX with actual Zenodo DOI after first release}
}
```

With:
```bibtex
@software{vromen2024lean,
  title={Formalizing Lewis's Theory of Common Knowledge in Lean 4},
  author={Vromen, Huub},
  year={2024},
  doi={10.5281/zenodo.1234567},
  url={https://github.com/yourusername/lewis-common-knowledge-lean4}
}
```

5. **Commit and push changes:**
```bash
git add README.md
git commit -m "Add Zenodo DOI badge"
git push origin main
```

## Understanding DOI Versioning

Zenodo provides TWO DOIs:

1. **Concept DOI** - Always points to the latest version
   - Example: `10.5281/zenodo.1234567`
   - Use this in most citations
   - Badge always shows "latest version"

2. **Version DOI** - Points to specific release
   - Example: `10.5281/zenodo.1234568` (v1.0.0)
   - Use when citing a specific version
   - Each release gets its own

**Recommendation:** Use the concept DOI in your README badge - it automatically updates.

## Future Releases

When you create future releases (v1.1.0, v2.0.0, etc.):

1. Create a new GitHub release as usual
2. Zenodo automatically:
   - Archives the new version
   - Creates a new version DOI
   - Updates the concept DOI to point to latest
3. No action needed - your badge updates automatically!

## Zenodo Metadata (Optional but Recommended)

You can enhance your Zenodo deposit with rich metadata:

1. Go to your Zenodo deposit
2. Click "Edit"
3. Add:
   - **Description:** Detailed project description
   - **Keywords:** lean4, formal-verification, common-knowledge, philosophy
   - **Related identifiers:** Link to your paper DOI
   - **License:** MIT (already detected from GitHub)
   - **Contributors:** Add any collaborators
4. Save changes

## Verifying Your DOI Works

Test your DOI:

1. Visit: `https://doi.org/10.5281/zenodo.YOUR_NUMBER`
2. Should redirect to your Zenodo page
3. Check that files are downloadable
4. Verify metadata is correct

## Adding DOI to Other Places

### Your CV
```
Software:
- Vromen, H. (2024). Formalizing Lewis's Theory of Common Knowledge in Lean 4.
  DOI: 10.5281/zenodo.1234567
```

### Your Website
```html
<a href="https://doi.org/10.5281/zenodo.1234567">
  <img src="https://zenodo.org/badge/DOI/10.5281/zenodo.1234567.svg" alt="DOI">
</a>
```

### Future Papers
```latex
\cite{vromen2024lean}
% In bibliography:
@software{vromen2024lean,
  author = {Vromen, Huub},
  title = {Formalizing Lewis's Theory of Common Knowledge in Lean 4},
  year = {2024},
  doi = {10.5281/zenodo.1234567}
}
```

## Troubleshooting

### "I don't see my repository in Zenodo"
- Make sure repository is public
- Check you're logged in with correct GitHub account
- Try refreshing the page
- Wait a few minutes for sync

### "Zenodo didn't archive my release"
- Check the repository toggle is ON in Zenodo
- Verify you created a proper GitHub release (not just a tag)
- Check your email for error notifications
- Wait 5-10 minutes for processing

### "I want to change the metadata"
- Go to your Zenodo deposit
- Click "Edit" (if not available, contact Zenodo support)
- Update metadata
- New versions can have updated metadata

### "Can I delete a DOI?"
- No - DOIs are permanent by design
- You can hide a deposit, but the DOI remains
- Be sure before creating your release!

## Best Practices

✅ **Do:**
- Create meaningful release notes
- Use semantic versioning (v1.0.0, v1.1.0, v2.0.0)
- Update metadata on Zenodo
- Link to your published paper
- Test the DOI after creation

❌ **Don't:**
- Create releases for minor changes (use v1.0.1, v1.0.2 for those)
- Rush - verify everything works first
- Forget to update README with actual DOI
- Use the version DOI in your badge (use concept DOI)

## Timeline

Here's a realistic timeline:

- **Day 1:** Publish to GitHub
- **Day 1 (1 hour later):** Link to Zenodo
- **Day 1-7:** Test build, verify everything works
- **Week 1:** Create v1.0.0 release
- **Week 1 (10 minutes later):** Zenodo creates DOI
- **Week 1:** Update README with DOI
- **Week 2:** Announce with DOI included

## Support

- **Zenodo Help:** https://help.zenodo.org/
- **Zenodo Support:** Contact via their support form
- **GitHub Releases:** https://docs.github.com/en/repositories/releasing-projects-on-github

## Example: Complete Flow

```bash
# 1. Ensure code is on GitHub
git push origin main

# 2. Go to Zenodo, link repository (web interface)

# 3. Create release
git tag -a v1.0.0 -m "Initial release"
git push origin v1.0.0

# 4. Create release on GitHub web interface

# 5. Wait for Zenodo (check email)

# 6. Update README
# Edit README.md to add DOI
git add README.md
git commit -m "Add Zenodo DOI"
git push origin main

# Done! Your formalization now has a permanent DOI
```

---

**Congratulations!** Once you have your DOI, your formalization is:
- ✅ Permanently archived
- ✅ Formally citable
- ✅ Professionally presented
- ✅ Part of the academic record

Your work will be discoverable and citable for decades to come!
