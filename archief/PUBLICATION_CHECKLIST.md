# Publication Readiness Checklist

## GitHub Repository (Before Publishing)

### Code Quality
- [x] All proofs complete (zero sorries) ✅
- [ ] Code follows Lean style guidelines
  - [ ] Consistent naming conventions
  - [ ] Proper indentation (2 spaces)
  - [ ] Line length < 100 characters where possible
  - [ ] Doc comments for all major definitions/theorems
- [ ] No unnecessary imports
- [ ] No unused variables/definitions
- [ ] Optimize proof tactics where possible (replace `aesop` with explicit steps if clearer)

### Documentation
- [x] README.md comprehensive and clear ✅
- [x] LICENSE file (MIT) ✅
- [x] CITATION.cff for easy citation ✅
- [ ] CONTRIBUTING.md (guidelines for contributions)
- [ ] CODE_OF_CONDUCT.md (standard for academic projects)
- [ ] Per-file documentation complete
  - [x] Vromen_justification_logic.lean ✅
  - [x] Sillari_refutation.lean ✅
  - [x] Cubitt_Sugden_baseline.lean ✅
- [ ] CHANGELOG.md (version history)

### Repository Structure
- [ ] Create proper directory structure:
  ```
  /
  ├── src/
  │   ├── Vromen_justification_logic.lean
  │   ├── Sillari_refutation.lean
  │   └── Cubitt_Sugden_baseline.lean
  ├── docs/
  │   ├── paper/  (LaTeX source when ready)
  │   ├── slides/ (presentation materials)
  │   └── bibliography.bib
  ├── paper/
  │   └── Vromen__2024__Reasoning_with_reasons_Lewis_on_common_knowledge.pdf
  ├── README.md
  ├── LICENSE
  ├── CITATION.cff
  ├── lakefile.lean
  ├── lean-toolchain
  └── .gitignore
  ```

### Technical Setup
- [ ] lakefile.lean configured correctly
- [ ] lean-toolchain specifies exact version
- [ ] .gitignore excludes build artifacts
  ```
  /build/
  /lake-packages/
  /.lake/
  .DS_Store
  *.olean
  ```
- [ ] CI/CD setup (GitHub Actions)
  - [ ] Automatic build verification on push
  - [ ] Automatic build verification on pull requests
  - [ ] Badge showing build status in README

### Examples of GitHub Actions Workflow
```yaml
# .github/workflows/build.yml
name: CI
on: [push, pull_request]
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: leanprover/lean-action@v1
        with:
          lake-build: true
```

### Metadata
- [ ] Add topics to GitHub repository:
  - common-knowledge
  - david-lewis
  - justification-logic
  - formal-verification
  - lean4
  - epistemic-logic
  - game-theory
  - philosophy
  - economics
- [ ] Repository description clear and concise
- [ ] Website link (if you have one)
- [ ] Create releases/tags for versions
  - [ ] v1.0.0 - Initial publication release

### Archival
- [ ] Get DOI from Zenodo
  1. Link GitHub repo to Zenodo
  2. Create release on GitHub
  3. Zenodo automatically archives and assigns DOI
  4. Update README with DOI badge
- [ ] Consider Software Heritage archival
- [ ] Update CITATION.cff with DOI

## Academic Paper

### Writing Phase

#### Abstract & Introduction
- [ ] Abstract (250 words)
  - [ ] States the problem clearly
  - [ ] Describes approach
  - [ ] Lists main results
  - [ ] Indicates significance
- [ ] Introduction (3-4 pages)
  - [ ] Motivates the problem (common knowledge puzzle)
  - [ ] Reviews Lewis's informal account
  - [ ] Explains why formalization matters
  - [ ] Previews three approaches
  - [ ] States main contributions explicitly
  - [ ] Provides roadmap

#### Main Content
- [ ] Background section complete
  - [ ] Lewis's theory explained clearly
  - [ ] Key concepts defined
  - [ ] Philosophical context provided
- [ ] Three approaches section complete
  - [ ] Each approach explained
  - [ ] Lean formalizations described
  - [ ] Results stated precisely
  - [ ] Comparisons drawn
- [ ] Technical results section complete
  - [ ] All theorems stated formally
  - [ ] Proof sketches provided
  - [ ] Key insights highlighted
  - [ ] Counterexamples explained clearly
- [ ] Philosophical implications section complete
  - [ ] Conceptual insights discussed
  - [ ] "Thereby" analysis
  - [ ] Reasons-as-objects argument
  - [ ] Broader significance explained
- [ ] Related work section complete
  - [ ] Comprehensive literature review
  - [ ] Proper positioning of contribution
  - [ ] Clear comparison with alternatives
- [ ] Future work section
  - [ ] Extensions outlined
  - [ ] Applications suggested
  - [ ] Open problems identified
- [ ] Conclusion
  - [ ] Results summarized
  - [ ] Contributions emphasized
  - [ ] Broader impact discussed

#### Technical Quality
- [ ] All mathematical notation defined
- [ ] All Lean code excerpts properly formatted
- [ ] All figures/diagrams clear and labeled
- [ ] All tables properly formatted
- [ ] Comparison table(s) included
- [ ] Proofs in appendices (if needed)
- [ ] No undefined abbreviations
- [ ] Consistent terminology throughout

#### References
- [ ] Bibliography complete (60-80+ items)
  - [ ] All Lewis references
  - [ ] All formalization attempts (Cubitt-Sugden, Sillari, Vromen)
  - [ ] Modal logic references
  - [ ] Justification logic references
  - [ ] Game theory references
  - [ ] Proof assistant references
  - [ ] Related philosophy references
- [ ] All citations formatted correctly (journal style)
- [ ] All in-text citations match bibliography
- [ ] No missing references
- [ ] URLs included where appropriate
- [ ] DOIs included for all recent papers

#### Formatting
- [ ] Follows journal guidelines exactly
  - [ ] Page limits respected
  - [ ] Margin/font specifications followed
  - [ ] Citation style correct
  - [ ] Section numbering style correct
- [ ] LaTeX source clean (if using LaTeX)
  - [ ] No commented-out chunks
  - [ ] Proper document class
  - [ ] All packages necessary and documented
- [ ] Figures/tables in correct format
  - [ ] High resolution (300+ DPI)
  - [ ] Proper captions
  - [ ] Referred to in text
- [ ] Appendices formatted correctly (if needed)

### Review Phase

#### Self-Review
- [ ] Read entire paper aloud (catches errors)
- [ ] Check logical flow (each paragraph follows from previous)
- [ ] Verify all claims are supported (evidence/proof/citation)
- [ ] Ensure no contradictions
- [ ] Check for repetition (remove or cross-reference)
- [ ] Verify technical accuracy (all Lean code correct)
- [ ] Test all claimed results in Lean
- [ ] Check all examples work as described

#### Colleague Review
- [ ] Get feedback from logician colleague
- [ ] Get feedback from philosopher colleague  
- [ ] Get feedback from formal methods colleague
- [ ] Get feedback from someone unfamiliar with topic (accessibility check)
- [ ] Incorporate feedback systematically
- [ ] Thank reviewers in acknowledgments

#### Technical Validation
- [ ] All Lean code compiles
- [ ] All theorems have proofs (zero sorries)
- [ ] All claimed results are actually proven
- [ ] No outdated code from earlier versions
- [ ] Repository linked in paper is public and accessible
- [ ] DOI in paper matches actual DOI

#### Proofreading
- [ ] Spell check (US or UK English, be consistent)
- [ ] Grammar check
- [ ] Check for typos in:
  - [ ] Theorem names
  - [ ] Author names
  - [ ] Journal names
  - [ ] URLs
- [ ] Check punctuation consistency
- [ ] Check capitalization consistency
- [ ] Remove any TODO/FIXME comments

### Submission Phase

#### Cover Letter (if required)
- [ ] Addressed to editor by name (research the journal)
- [ ] States what paper is about (1 paragraph)
- [ ] States significance (1 paragraph)
- [ ] Explains why this journal (1 paragraph)
- [ ] Mentions any relevant presentations (adds credibility)
- [ ] Suggests potential reviewers (if allowed)
- [ ] Lists any conflicts of interest
- [ ] Confirms paper is original and not under review elsewhere

#### Supplementary Materials
- [ ] Link to GitHub repository (in paper and submission system)
- [ ] Link to DOI (Zenodo)
- [ ] Any extended proofs (if not in paper)
- [ ] Any additional figures/tables (if not in paper)
- [ ] Demo video (if appropriate)

#### Journal Selection

**Criteria to consider:**
- [ ] Fit with journal scope (read recent issues)
- [ ] Journal prestige (impact factor, reputation)
- [ ] Publication timeline (some journals are slow)
- [ ] Open access options (if desired/required)
- [ ] Page limits (some journals very restrictive)
- [ ] Audience reach (who reads this journal?)

**Top choices for this paper:**
1. **Journal of Philosophical Logic** (Tier 1)
   - Perfect fit (logic + philosophy)
   - Publishes formal work regularly
   - High prestige
   
2. **Economics & Philosophy** (Tier 1)
   - Published original Vromen paper
   - Interest in common knowledge
   - Interdisciplinary
   
3. **Journal of Formalized Reasoning** (Specialized)
   - Focuses on verified mathematics/logic
   - Appreciates Lean work
   - Growing prestige
   
4. **Synthese** (Tier 2)
   - Published Sillari's work
   - Interested in formalization
   - Broader audience

#### Submission System
- [ ] Create account in journal system
- [ ] Fill out all required metadata
  - [ ] Title
  - [ ] Abstract
  - [ ] Keywords (5-7 usually)
  - [ ] Author information (name, affiliation, email, ORCID)
  - [ ] Suggested reviewers (3-5 usually)
  - [ ] Excluded reviewers (if conflicts)
- [ ] Upload main document (PDF)
- [ ] Upload supplementary materials (if separate)
- [ ] Upload cover letter (if required)
- [ ] Agree to terms (copyright, originality, etc.)
- [ ] Submit!

### Post-Submission

#### Immediate
- [ ] Save submission confirmation email
- [ ] Note submission date
- [ ] Save all submitted files (in case of resubmission)
- [ ] Update CV with "under review at [journal]"
- [ ] Update GitHub README with "paper under review"

#### During Review (typically 2-4 months)
- [ ] Be patient
- [ ] Don't pester editor (unless >6 months with no word)
- [ ] Respond promptly to any queries
- [ ] Continue working on related projects
- [ ] Present at conferences if accepted
- [ ] Monitor for reviewer requests (in case you're asked to review related work)

#### If Rejected
- [ ] Read reviews carefully (even if harsh)
- [ ] Extract constructive feedback
- [ ] Discuss with colleagues
- [ ] Revise paper addressing concerns
- [ ] Select next target journal
- [ ] Resubmit within 1-2 months (momentum matters)
- [ ] Update cover letter mentioning revisions

#### If Accepted with Revisions (most likely outcome)
- [ ] Read all reviewer comments carefully
- [ ] Make list of required changes
- [ ] Prioritize major concerns
- [ ] Address every comment (even if you disagree)
- [ ] Write detailed response letter
  - [ ] Thank reviewers
  - [ ] Address each comment specifically
  - [ ] Explain changes made
  - [ ] Politely explain if you didn't make a suggested change
- [ ] Revise paper
- [ ] Highlight changes (if journal requires)
- [ ] Resubmit within deadline (usually 1-3 months)
- [ ] Update GitHub with revised version (optional during review)

#### If Accepted
- [ ] Celebrate! 🎉
- [ ] Sign copyright transfer (if required)
- [ ] Submit final version
- [ ] Provide any additional materials requested
- [ ] Proofread page proofs carefully
- [ ] Correct any errors in proofs
- [ ] Provide ORCID, funding info, etc.
- [ ] Pay publication fees (if OA)

### Post-Publication

#### Immediate
- [ ] Update CV with publication details
- [ ] Update GitHub README with publication info
  - [ ] Add "Published in [journal]" badge
  - [ ] Link to published version
  - [ ] Link to preprint (if different)
- [ ] Add paper to:
  - [ ] Personal website
  - [ ] Google Scholar
  - [ ] ResearchGate
  - [ ] Academia.edu
  - [ ] PhilPapers (for philosophy papers)
  - [ ] arXiv (if permitted - check journal policy)
- [ ] Tweet/post about publication (if you use social media)
- [ ] Share with colleagues who helped
- [ ] Thank everyone in acknowledgments personally

#### Ongoing
- [ ] Respond to questions about the work
- [ ] Cite others who cite you (builds relationships)
- [ ] Monitor citations (Google Scholar alerts)
- [ ] Update GitHub if errors found
- [ ] Consider blog post explaining main ideas (broader audience)
- [ ] Consider YouTube video explaining paper
- [ ] Present at more venues if invited
- [ ] Build on the work (next paper!)

## Conference Presentation

### Abstract Submission
- [ ] Abstract written (150-500 words depending on conference)
- [ ] Keywords selected
- [ ] Format matches conference requirements
- [ ] Submitted before deadline
- [ ] Confirmation email saved

### If Accepted

#### Pre-Conference Preparation
- [ ] Slides created (see CONFERENCE_ABSTRACT.md for outline)
- [ ] Live demo tested multiple times
- [ ] Backup demo video created
- [ ] Handouts prepared (if allowed)
- [ ] Talk practiced 3+ times
  - [ ] Alone
  - [ ] With colleagues
  - [ ] Record yourself and watch
- [ ] Timing verified (stay within limits!)
- [ ] Questions anticipated and answers prepared
- [ ] Travel/accommodation booked
- [ ] Conference registration paid

#### Materials to Bring
- [ ] Laptop (fully charged)
- [ ] All necessary adapters (HDMI, VGA, USB-C, etc.)
- [ ] Backup of slides (USB drive + cloud)
- [ ] Backup laptop (or trusted colleague's)
- [ ] Printed notes (in case of tech failure)
- [ ] Business cards (for networking)
- [ ] Handouts (if prepared)
- [ ] Phone charger
- [ ] Conference schedule

#### At Conference
- [ ] Arrive at session early
- [ ] Test equipment
- [ ] Have water available
- [ ] Breathe and relax
- [ ] Deliver talk
- [ ] Answer questions graciously
- [ ] Network afterward
- [ ] Attend other talks (learn and be seen)
- [ ] Take notes on feedback

#### Post-Conference
- [ ] Follow up with interested people
- [ ] Incorporate feedback into paper
- [ ] Update GitHub with "presented at [conference]"
- [ ] Write blog post about experience
- [ ] Consider submitting to journal
- [ ] Thank organizers

## Ongoing Maintenance

### GitHub Repository
- [ ] Respond to issues within 1 week
- [ ] Review pull requests within 2 weeks
- [ ] Keep dependencies updated
  - [ ] Lean version
  - [ ] Mathlib version
- [ ] Fix bugs as discovered
- [ ] Add new features if valuable
- [ ] Update documentation as code evolves
- [ ] Create new releases for major updates

### Community Engagement
- [ ] Answer questions on:
  - [ ] GitHub issues
  - [ ] Lean Zulip chat
  - [ ] Stack Overflow (if relevant questions)
- [ ] Write blog posts about:
  - [ ] How to use the formalization
  - [ ] Interesting discoveries
  - [ ] Lessons learned
- [ ] Give talks about the work
- [ ] Teach others (tutorials, workshops)
- [ ] Collaborate with interested researchers

## Quality Metrics

### Code Quality Indicators
- ✅ Zero sorries (all proofs complete)
- ✅ Compiles without warnings
- ✅ No unused imports
- ✅ No unused variables
- ✅ Consistent naming
- ✅ Comprehensive documentation
- ✅ Good test coverage (via examples)

### Publication Readiness Indicators
- [ ] All sections complete (no TODOs)
- [ ] All claims proven or cited
- [ ] All figures/tables polished
- [ ] Multiple rounds of review completed
- [ ] Formatting matches journal exactly
- [ ] Length within journal limits
- [ ] Supplementary materials ready
- [ ] Cover letter written

### Presentation Readiness Indicators
- [ ] Talk fits in time limit
- [ ] Practiced 3+ times
- [ ] Technical demos tested
- [ ] Backup plans ready
- [ ] Q&A preparation done
- [ ] Materials printed/prepared
- [ ] Logistics confirmed

## Final Pre-Submission Checklist

### Critical Items (Must Complete)
- [ ] Code compiles with zero errors
- [ ] All theorems proven (zero sorries)
- [ ] README comprehensive
- [ ] GitHub repository public
- [ ] DOI obtained (Zenodo)
- [ ] Paper complete (no TODOs)
- [ ] Bibliography complete
- [ ] All figures/tables final
- [ ] Formatting correct
- [ ] Proofreading complete
- [ ] Self-review done
- [ ] Colleague review done
- [ ] All claimed results verified

### Recommended Items (Strongly Advised)
- [ ] CI/CD setup (automated testing)
- [ ] CONTRIBUTING.md
- [ ] CODE_OF_CONDUCT.md
- [ ] CHANGELOG.md
- [ ] Extended documentation
- [ ] Blog post drafted
- [ ] Demo video created
- [ ] Social media announcement prepared

### Optional Items (Nice to Have)
- [ ] Interactive tutorial
- [ ] Visualization tools
- [ ] Jupyter notebook examples
- [ ] Slides for multiple audiences
- [ ] FAQ document
- [ ] Comparison with other proof assistants
- [ ] Performance benchmarks

---

## Timeline Template

**Months 1-2: Finalization**
- Week 1-2: Code cleanup and documentation
- Week 3-4: GitHub setup and archival
- Week 5-6: Paper first draft
- Week 7-8: Paper self-review and revision

**Month 3: Review and Polish**
- Week 9-10: Colleague review
- Week 11: Incorporate feedback
- Week 12: Final proofreading

**Month 4: Submission**
- Week 13: Submit to journal
- Week 13: Submit to conference (if timeline aligns)
- Week 14-16: Start next project while waiting

**Months 5-8: Review Period**
- Be patient
- Respond to queries
- Present at conferences

**Months 9-12: Revision and Publication**
- Address reviewer comments
- Revise and resubmit
- Correct proofs
- Celebrate publication!

---

## Success Indicators

✅ **Code Ready**: Compiles, documented, public, archived  
✅ **Paper Ready**: Complete, reviewed, formatted, proofread  
✅ **Presentation Ready**: Slides done, practiced, tested  
✅ **Community Ready**: Open to contributions, responsive, collaborative

**When all checked, you're ready to publish!** 🚀
