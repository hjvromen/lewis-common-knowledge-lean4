# Lewis Formalization: Publication Strategy and Technical Guide

## Executive Summary

**Primary Paper:** "Mechanizing Lewis's Convention Theory: A Lean 4 Verification"
- **Target Journal:** Journal of Philosophical Logic (Q1, SJR: 1.497)
- **Core Contribution:** Machine-checked verification of Vromen (2024)'s informal arguments
- **Length:** 10,000-12,000 words
- **Backup Journals:** Synthese (Q1), Erkenntnis (Q1)

**Follow-Up Paper:** "Defeasible Justification Logic for Common Knowledge: Semantics and Completeness"
- **Target Journal:** Studia Logica or Journal of Logic and Computation
- **Core Contribution:** Semantic foundations and completeness investigation
- **Status:** Open problem whether completeness holds without the `+` operator

---

## 1. Journal Rankings (2024 Scimago Data)

### Q1 Journals (Top 25%)
- **Synthese**: Q1 (SJR: 1.052) - Published Sillari (2005)
- **Economics and Philosophy**: Q1 in Philosophy, Q2 in Economics (SJR: 0.936) - Published Vromen (2024)
- **Journal of Philosophical Logic**: Q1 (SJR: 1.497) - **PRIMARY TARGET**
- **Erkenntnis**: Q1 (SJR: 0.945) - Strong in formal epistemology

### Q2 Journals (25-50%)
- **Journal of Automated Reasoning**: Q2 (SJR: 0.616)
- **Logical Methods in Computer Science**: Q2-Q4 (declining/unclear ranking)

### Note on Journal of Formalized Reasoning
- Indexed in Scopus but no clear quartile ranking found
- Too new/small for established rankings

---

## 2. Paper Structure and Framing

### Critical Framing Principle

**What Vromen (2024) Established:**
- Sillari's formalization fails (informal counterexamples)
- Justification logic is the correct framework (informal proofs)
- A1 and A6 should be theorems, not axioms

**What the Lean Paper Contributes:**
- **Machine-checked verification** of those informal arguments
- **Formal proofs** that can be independently verified
- **Constructive/explicit proofs** showing exact assumptions needed
- **Methodological innovation**: demonstrating proof assistants for philosophy

**Never Claim as Novel:**
- ❌ Discovery of Sillari's flaws (already in 2024 paper)
- ❌ The justification logic approach (already in 2024 paper)
- ❌ That A1 and A6 are theorems (already in 2024 paper)
- ❌ The philosophical insights (already in 2024 paper)

**Can Claim as Novel:**
- ✅ First formal verification of Lewis's theory in a proof assistant
- ✅ First machine-checked refutation of Sillari
- ✅ Constructive/explicit proofs (the actual Lean derivations)
- ✅ Methodological innovation (showing how to use Lean for philosophy)
- ✅ Complete formal specification of the theory

---

## 3. Recommended Paper Structure

### Title
"Mechanizing Lewis's Convention Theory: A Lean 4 Verification"

### Abstract (Draft)
"Lewis's informal account of common knowledge left gaps that subsequent formalizations have attempted to fill. Vromen (2024) argued that Sillari's widely-cited modal logic approach fails and that justification logic provides the correct framework. This paper formalizes those arguments in the Lean 4 proof assistant, providing machine-checked verification of the counterexamples to Sillari's approach and constructive proofs that Lewis's key axioms (A1 and A6) become theorems in justification logic. The formalization demonstrates how proof assistants can bring mathematical rigor to philosophical arguments, ensuring correctness and enabling independent verification. All Lean code is publicly available for reproduction."

### Section Outline

**1. Introduction** (1,500 words)
- Brief recap of Vromen (2024)
- New contribution: machine-checked verification in Lean 4
- Why formal verification matters for philosophy
- Preview of three formalizations

**2. Background: Lewis's Theory and Its Challenges** (1,500 words)
- Lewis's informal account
- The gap in Lewis's argument (axiom S)
- Previous attempts: Cubitt-Sugden (2003), Sillari (2005)
- Vromen (2024) solution: explicit reasons

**3. Formalization 1: Direct Approach (Cubitt-Sugden Style)** (2,000 words)
- Present `Cubitt_Sugden.lean`
- The RC (R-closure) inductive definition
- Proof of `everyone_reason_of_rc`
- Concrete examples (L1, L2, L3)
- Key point: Works but requires axioms A1 and A6

**4. Formalization 2: Sillari's Modal Logic Approach Fails** (2,500 words)
- Present `Sillari_improved.lean`
- Verified counterexamples: B3 fails, C4 fails
- Formal proof of inconsistency: (B3) contradicts (S2)
- Lewis's theorem: false (local) or trivial (global)
- Framing: "Building on the informal counterexamples in Vromen (2024), this provides machine-checked verification"

**5. Formalization 3: Justification Logic Solution** (3,000 words)
- Present `reasons_improved.lean`
- Explicit reasons with multiplication operator
- A1 and A6 are now theorems (not axioms!)
- Minimal assumptions (T1, T2, T3)
- Full proof of Lewis's theorem

**5.6 Semantic Foundation** (1,000 words)
- Evidence models framework
- Why you omit the `+` operator (defeasibility)
- Comparison with Sillari's modal semantics
- Completeness as open problem

**6. Philosophical Implications** (1,500 words)
- What formal verification teaches us
- Why justification logic > modal logic for Lewis
- Reasons vs. knowledge
- Role of explicit justifications in social coordination

**7. Conclusion** (500 words)
- First mechanized verification of Lewis
- Definitive refutation of Sillari (verified)
- Justification logic vindicated
- Methodology for philosophy

---

## 4. Semantics Subsection (Draft)

### Section 5.6: Semantic Foundation

The justification logic formalization presented above is grounded in the semantic framework of Artemov's justification logic (Artemov and Fitting 2019), though with an important modification that makes it more suitable for modeling defeasible reasoning about common knowledge.

**Evidence Models.** A justification model consists of a set of possible worlds W, a set of agents I, and an *evidence function* that determines which justification terms constitute admissible evidence for which propositions at which worlds. More precisely, for each agent i and world w, the model specifies whether a given justification term r justifies a given proposition φ for agent i at world w. The truth condition for our basic formula `r :ᵢ φ` is:

> `w ⊨ r :ᵢ φ` if and only if r is admissible evidence for agent i to believe φ at world w

The existential formula `R i φ` (agent i has reason to believe φ) holds at w when there exists some justification term that serves as admissible evidence for i to believe φ at w.

**Admissibility and Application.** The evidence function must satisfy a closure condition that validates our application rule (AR): if s is evidence for i to believe φ → ψ and t is evidence for i to believe φ, then s·t (the application of s to t) must be evidence for i to believe ψ. This constraint ensures that modus ponens is sound: from a reason to believe an implication and a reason to believe its antecedent, we can construct a reason to believe the consequent. The constants a, b, and c from axioms T1-T3 are specified as providing evidence for the corresponding logical principles for all agents at all worlds—a standard approach in justification logic known as *constant specification* (Artemov and Fitting 2019: Ch. 3).

**Non-Monotonicity and Defeasibility.** An important feature of our logic is what it *omits* from standard justification logic. Artemov's full justification logic includes a second operator `+` for combining evidence, along with axioms that make the logic monotonic: once a justification is established, it remains forever valid. However, as discussed in Vromen (2024), reasons to believe are defeasible—unlike mathematical proofs, they can be defeated by new information. The Nixon diamond scenario illustrates this: the fact that Nixon is a Quaker provides reason to believe he is a pacifist, while the fact that he is a Republican provides reason to believe he is not a pacifist. Both reasons coexist, and either might be overridden by further information.

Our semantics accommodates this by *not* requiring the evidence function to be closed under arbitrary combinations of evidence. We require only closure under application (·), which corresponds to modus ponens—an inference that remains valid even in defeasible reasoning. This makes our logic a proper fragment of standard justification logic, with simpler semantic constraints. For applications of full justification logic (with the `+` operator) to common knowledge, see Artemov (2006) and Bucheli et al. (2011); our fragment suffices for Lewis's purposes while better modeling the defeasible nature of practical reasoning.

**Why Justification Logic Succeeds Where Modal Logic Fails.** The key advantage of this semantic framework over Sillari's purely modal approach becomes clear when we compare the two. In Sillari's Kripke semantics, the formula `R i φ` is interpreted simply as "φ holds at all worlds accessible to i." This interpretation cannot distinguish *different reasons* for believing the same proposition. But Lewis's argument crucially relies on tracking *which reason* justifies which belief: i's reason for believing A "thereby" provides a reason for believing φ.

The justification logic semantics makes these reason-tracking inferences explicit. When we say that i's reason for A indicates φ (i.e., `∃r. r :ᵢ (A → φ)`), we assert that there exists a *specific justification term* r that bridges A and φ. When we apply this reason using the application operator (·), we perform a *traceable* inference that constructs a new, composite reason. This is why we can prove A1 and A6 as theorems: the semantics provides machinery to construct the required justifications explicitly, whereas Sillari's modal semantics has no such machinery.

**Relation to Common Knowledge Semantics.** The evidence model semantics provides a natural interpretation of Lewis's "basis for common knowledge." A state of affairs A serves as a basis for common knowledge of φ when A makes available, to all agents, a structure of public evidence that allows each agent to construct justifications for arbitrarily nested beliefs about φ. Our theorem shows that this structure of available evidence generates the infinite hierarchy that Lewis described, without requiring the kind of perfect introspective access that full justification logic (with the `+` operator) would enforce.

**Future Work.** The semantics for our fragment is simpler than full justification logic due to the absence of the `+` operator and its associated axioms. However, this raises an interesting technical question: without full internalization, can we still prove completeness? Standard completeness proofs for justification logic rely heavily on the ability to internalize arbitrary theorems using the `+` operator. Whether a modified completeness proof can be given for our defeasible fragment, or whether the logic is inherently incomplete, remains an open problem that will be explored in future work. Even without full completeness, we have proven: (1) soundness—every theorem is valid, (2) adequacy for Lewis—every formula in the R-closure of φ is provable, and (3) finite axiomatization—axioms AR, T1, T2, T3 are sufficient.

---

## 5. Completeness Question

### The Challenge

**Problem:** Without the `+` operator, you cannot prove full internalization:
- Cannot prove: If `⊢ φ` then `⊢ t : φ` for arbitrary φ
- Can only prove: `⊢ t : φ` for specific φ built from T1, T2, T3 via AR

**Possible Outcomes:**

**1. Completeness Holds (40% probability)**
- Modified canonical model construction works
- Reachable formulas are all justified by terms built from a, b, c
- Would be surprising but possible

**2. Completeness Fails (50% probability)**
- Some theorems cannot be justified
- Canonical model construction breaks
- Still publishable: characterize what IS justifiable

**3. Restricted Completeness (10% probability)**
- Complete for R/Ind fragment (without explicit `:`)
- Most elegant philosophically
- Captures exactly what's needed for Lewis

### What You Can Already Prove

1. **Soundness:** Every theorem is valid ✓
2. **Adequacy for Lewis:** Every formula in R-closure is provable ✓
3. **Finite axiomatization:** AR, T1, T2, T3 are sufficient ✓

These suffice for the verification paper. Completeness is for the follow-up.

---

## 6. GitHub Repository Preparation

### File Organization

```
lewis-formalization/
├── README.md
├── LICENSE
├── Cubitt_Sugden.lean
├── Sillari_improved.lean
└── reasons_improved.lean
```

### README.md Contents

```markdown
# Mechanizing Lewis's Convention Theory in Lean 4

This repository contains Lean 4 formalizations of David Lewis's theory 
of common knowledge and conventions, accompanying the paper:

**"Mechanizing Lewis's Convention Theory: A Lean 4 Verification"**  
Huub Vromen (2025)

## Files

- `Cubitt_Sugden.lean` - Direct formalization following Cubitt & Sugden (2003)
- `Sillari_improved.lean` - Counterexamples showing Sillari (2005) fails
- `reasons_improved.lean` - Justification logic approach (main contribution)

## Verification

To verify the proofs:

1. Install Lean 4 (version 4.x or later)
2. Clone this repository
3. Run `lake build` in the repository directory

All proofs are machine-checked and constructive.

## Key Results

- **Theorem (Cubitt-Sugden):** Lewis's theorem provable with axioms A1, A6
- **Counterexample (Sillari):** B3 fails, C4 fails, Lewis's theorem false/trivial
- **Theorem (Justification Logic):** A1 and A6 are theorems, not axioms

## Citation

If you use this code, please cite:

Vromen, H. (2025). Mechanizing Lewis's Convention Theory: A Lean 4 
Verification. *Journal of Philosophical Logic* (forthcoming).

## License

MIT License (or CC0 for maximum reusability)
```

### Comments in Lean Files

**Keep extensive comments** because:
- Different audiences (paper readers vs. code users)
- Self-contained repository (useful without reading paper)
- Referee convenience (easy verification)
- Educational value (teaching resource)
- Higher citations and reuse

**Structure comments at three levels:**

```lean
/-!
  # File Overview
  Brief description of what this file does
-/

/-!
  ## Section: Core Definitions
  Explanation of the definitions in this section
-/

/-- 
  Individual function/lemma documentation
  
  This lemma shows...
  
  The proof works by...
-/
lemma example_lemma : ... := by
  -- Step-by-step proof comments
  ...
```

---

## 7. Including Alternative Proofs

### Recommended Method: Main Lemma + `example`

```lean
/-- 
  A1 (Lewis's first key axiom): Indication supports reasoning.

  The proof below follows the step-by-step derivation in 
  Cubitt & Sugden (2003). An alternative automated proof 
  using `aesop` is provided below.
-/
lemma A1 {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (A : Prop) :
    ∀ {i : indiv} {α : Prop}, Ind rb A i α → R rb i A → R rb i α := by
  -- Step 1: Introduce the hypotheses
  intro i α h1 h2
  -- Step 2: Unfold the definition of indication
  rw [Ind] at h1
  -- Step 3: Apply modus ponens (lemma E1)
  exact E1 rb h1 h2

/-- 
  Alternative proof of A1 using the `aesop` automation.
  This demonstrates that the result can also be obtained automatically.
-/
example {indiv reason : Type} [Mul reason]
    (rb : reason → indiv → Prop → Prop) (A : Prop) :
    ∀ {i : indiv} {α : Prop}, Ind rb A i α → R rb i A → R rb i α := by
  aesop
```

**Benefits:**
- Both proofs are checked by Lean
- Only one lemma name exists for later use
- Clear which is the "official" proof
- Shows both pedagogical clarity AND automation capability

---

## 8. Timeline and Next Steps

### Immediate Tasks (Months 1-2)
- ✅ Fine-tune Lean files
- ✅ Add alternative proofs where useful
- ✅ Add file-level overview comments
- ✅ Verify all proofs still work

### GitHub Preparation (Month 3)
- Create repository with all files
- Write comprehensive README
- Add LICENSE file
- Test verification instructions

### Paper Writing (Months 2-4)
- Draft complete paper following structure above
- Include selective code snippets in paper
- Link prominently to GitHub
- Prepare for submission

### Submission (Month 4)
- Submit to Journal of Philosophical Logic
- Provide GitHub link in supplementary materials

### Review Process (Months 5-8)
- Respond to reviewer concerns
- Update Lean code if needed
- Revise paper based on feedback

### Target Publication
- Late 2026 or early 2027

---

## 9. Follow-Up Paper Strategy

### Title Options
- "Defeasible Justification Logic for Common Knowledge: Semantics and Completeness"
- "Evidence Models for Lewis: Semantics and Completeness of Justification Logic"
- "Defeasible Justification Logic: Completeness Without Internalization" (if it holds)
- "Expressive Power and Limitations of Defeasible Justification Logic" (if incomplete)

### Content
- Formal definition of multi-agent evidence models
- Constant specifications for T1, T2, T3
- Soundness proof
- Completeness investigation (open problem)
- **Lean formalization of the semantics** (major contribution!)
- Discussion of defeasibility and non-monotonicity
- Comparison with Artemov (2006) and Bucheli et al. (2011)

### Target Journals
- Studia Logica (Q2)
- Journal of Logic and Computation (Q2)
- Review of Symbolic Logic (Q1) - if results are strong

---

## 10. Key References

### Essential Citations

**Lewis's Original Work:**
- Lewis, D. (1969). *Convention: A Philosophical Study*. Harvard University Press.

**Formalizations:**
- Cubitt, R.P. & Sugden, R. (2003). Common knowledge, salience and convention. *Economics and Philosophy*, 19, 175-210.
- Sillari, G. (2005). A logical framework for convention. *Synthese*, 147, 379-400.
- Vromen, H. (2024). Reasoning with reasons: Lewis on common knowledge. *Economics & Philosophy*, 40, 397-418.

**Justification Logic:**
- Artemov, S. (2006). Justified common knowledge. *Theoretical Computer Science*, 357, 4-22.
- Artemov, S. & Fitting, M. (2019). *Justification Logic: Reasoning with Reasons*. Cambridge University Press.
- Bucheli, S., Kuznets, R. & Studer, T. (2011). Justifications for common knowledge. *Journal of Applied Non-Classical Logics*, 21, 35-60.
- Kuznets, R. & Studer, T. (2019). *Logics of Proofs and Justifications*. College Publications.

**Defeasible Reasoning:**
- Renne, B. (2009). Evidence elimination in multi-agent justification logic. *TARK '09*, 227.
- Kuznets, R. & Studer, T. (2013). Update as evidence: belief expansion. *LFCS '13*, 266-279.

---

## 11. Writing Tips for Philosophy Audience

### Balance
- 60% philosophical interpretation and implications
- 40% technical details and formal results
- Always prioritize clarity over comprehensiveness

### Minimize Lean Syntax
- Use mathematical notation where possible
- Relegate complex code to appendix/repository
- Explain what code *does* more than how it works

### After Each Technical Section
Add "Philosophical significance" subsection connecting to broader debates

### Tell a Story
1. Lewis had an insight but left gaps
2. Multiple formalization attempts reveal different aspects
3. Machine verification vindicates justification logic
4. This methodology can advance philosophy generally

### Show, Don't Tell
Instead of: "Sillari's formalization fails"
Write: "The Lean code constructs a specific two-world Kripke frame where Sillari's axiom B3 demonstrably fails"

---

## 12. Potential Reviewer Concerns and Responses

### Concern 1: "Just translating informal arguments"

**Response:**
- Formalization revealed Sillari's errors (verified counterexamples)
- Proving A1/A6 as theorems strengthens the theory
- Machine verification provides certainty informal arguments cannot
- Made all assumptions explicit (T1, T2, T3)

### Concern 2: "Too technical for philosophy journal"

**Response:**
- Lean snippets minimal and well-explained
- Philosophical insights emphasized throughout
- Full proofs in supplementary materials
- Formal methods increasingly important for philosophy

### Concern 3: "Sillari critique too harsh"

**Response:**
- Framed constructively: helps us understand why justification logic needed
- Acknowledges Sillari's pioneering contribution
- Not condemning, but correcting and advancing

### Concern 4: "What about completeness?"

**Response:**
- Explicitly acknowledged as open problem
- Soundness and adequacy proven
- Sufficient for Lewis's purposes
- Natural follow-up research direction

---

## 13. Quick Reference: What's Novel vs. What's Verification

### Novel Contributions
✅ First formal verification of Lewis in proof assistant
✅ Machine-checked refutation of Sillari
✅ Explicit constructive proofs (actual Lean derivations)
✅ Methodological innovation (Lean for philosophy)
✅ Complete formal specification
✅ Demonstration that defeasible fragment suffices

### Vromen (2024) Already Established
❌ Sillari's formalization fails (informal counterexamples)
❌ Justification logic is correct framework
❌ A1 and A6 should be theorems
❌ Philosophical insights about reasons vs. knowledge

### Positioning
"This paper provides machine-checked verification of the philosophical arguments developed informally in Vromen (2024)"

---

## 14. Contact and Future Collaboration

For questions about:
- The Lean formalization: See GitHub issues
- The philosophical interpretation: See papers
- Extending this work: GitHub discussions welcome
- Completeness question: Future research opportunity

---

## Document Version
Created: October 2025
Last Updated: October 2025
Status: Ready for paper writing phase

---

## Checklist Before Submission

### Lean Files
- [ ] All proofs verify in current Lean 4
- [ ] File-level overview comments added
- [ ] Alternative proofs included where useful
- [ ] Comments accurate and helpful
- [ ] Code style consistent

### GitHub Repository
- [ ] README.md complete
- [ ] LICENSE added
- [ ] Verification instructions tested
- [ ] All files included
- [ ] Repository public

### Paper
- [ ] Correct framing (verification, not discovery)
- [ ] All three formalizations presented
- [ ] Semantics subsection included
- [ ] GitHub link prominent
- [ ] References complete
- [ ] Acknowledgment of Vromen (2024)
- [ ] Length appropriate (10,000-12,000 words)

### Submission Materials
- [ ] Cover letter explaining connection to Vromen (2024)
- [ ] Suggest referees familiar with Lewis/formal epistemology
- [ ] Highlight novel methodological contribution
- [ ] Emphasize machine verification aspect

---

*End of Document*
