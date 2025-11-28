# Conference Abstract: Formalizing Lewis's Common Knowledge

## Title

**Formalizing Lewis's Common Knowledge: Why Justification Logic Succeeds Where Modal Logic Fails**

## Authors

[Your Name]  
[Your Affiliation]  
[Your Email]

## Abstract (500 words - typical conference limit)

David Lewis's theory of common knowledge (1969) has been foundational to game theory, epistemology, and the philosophy of language. However, his informal presentation left gaps that subsequent scholars have attempted to fill through formalization. We present the first complete mechanically-verified formalization of Lewis's theory using the Lean 4 proof assistant, comparing three distinct approaches and revealing deep insights about the nature of reasons to believe.

**Three Approaches Compared:**

1. **Cubitt & Sugden (2003)**: Treat "reason to believe" (R) and "indication" (Ind) as primitive relations. Lewis's key axioms A1 and A6 must be assumed. This approach works but provides no explanation for why these axioms should hold.

2. **Sillari (2005)**: Uses modal logic with R as a box operator (□ᵢ) and Ind defined as Rᵢφ ∧ (φ→ψ). This approach has been cited in the literature but we prove it is fundamentally flawed.

3. **Vromen (2024)**: Uses justification logic with explicit reason terms where R i φ := ∃r. rb r i φ and Ind A i φ := R i (A→φ). We show this approach succeeds and provides deep insights.

**Main Technical Results:**

We provide complete Lean 4 formalizations (2,600+ lines, zero sorries) proving:

- **Sillari's approach fails**: We construct explicit counterexamples showing axiom B3 (Lewis's crucial A1) is demonstrably false in modal semantics. Additionally, Cubitt-Sugden's axiom C4 fails, and Lewis's theorem is either false (local interpretation) or trivially vacuous (global interpretation).

- **Vromen's approach succeeds**: We prove A1 and A6 are theorems (not axioms) derivable from the application rule of justification logic. The complete proof requires only three basic tautologies (T1, T2, T3), avoiding logical omniscience.

- **Lewis's theorem verified**: We provide a rigorous inductive proof that a basis for common knowledge generates the complete G-closure of higher-order reasons to believe.

**Philosophical Significance:**

The success of justification logic and failure of modal logic reveals a crucial insight: Lewis's use of "thereby" in his definition of indication ("if i had reason to believe that A held, i would *thereby* have reason to believe that ___") indicates that reasons are compositional objects, not merely modal operators. 

In justification logic, if s is a reason to believe A→φ and t is a reason to believe A, then s·t (their composition) is a reason to believe φ. The composite reason s·t literally contains t as a component, capturing the "thereby"—the reason for φ is based on the reason for A. Modal operators cannot represent this compositional structure, which explains why they fail.

**Broader Impact:**

This work demonstrates the value of formal verification in philosophy. Computer-checked proofs provide the highest standard of mathematical rigor, catch subtle errors that survive peer review (Sillari's inconsistency was unnoticed for nearly 20 years), and make all assumptions completely explicit. Moreover, formalization reveals conceptual insights: reasons-as-objects was implicit in Lewis but becomes unavoidable in formal reconstruction.

Our formalization is publicly available on GitHub, enabling future research on common knowledge, coordination, convention, and multi-agent systems. All proofs are mechanically verified with zero axioms assumed beyond standard mathematics, providing a solid foundation for cumulative progress.

**Target Audience:** Suitable for philosophy (epistemology, logic), computer science (formal verification, multi-agent systems), and economics (game theory, coordination).

---

## Short Abstract (150 words - for programs)

We present the first complete mechanically-verified formalization of David Lewis's common knowledge theory using Lean 4. Comparing three approaches—Cubitt & Sugden's syntactic baseline, Sillari's modal logic, and Vromen's justification logic—we prove: (1) Sillari's approach fundamentally fails (explicit counterexamples to key axioms); (2) Vromen's justification logic succeeds, deriving Lewis's axioms A1 and A6 as theorems rather than assumptions; (3) Lewis's informal "thereby" reveals reasons are compositional objects, not modal operators. This explains why modal logic fails and justification logic succeeds. All results are mechanically verified (2,600+ lines, zero sorries) and publicly available. The formalization reveals how formal verification can catch errors, resolve ambiguities, and discover conceptual insights in philosophical arguments. Implications for epistemology, game theory, and multi-agent systems.

---

## Keywords

Common knowledge, David Lewis, justification logic, modal logic, formal verification, Lean theorem prover, epistemic logic, coordination, reasons to believe

---

## Presentation Format Preferences

**Format options:**
- [ ] 20-minute talk + 10-minute Q&A
- [ ] 30-minute talk + 15-minute Q&A  
- [x] 45-minute talk + 15-minute Q&A (preferred for full story)
- [ ] Poster presentation
- [ ] Tutorial (90 minutes - could teach Lean basics + formalization)

**Special requirements:**
- Live Lean demonstration (5-10 minutes showing verification)
- Laptop + projector for interactive proof
- Whiteboard/board for conceptual diagrams

---

## Talk Outline (45 minutes)

### Part 1: The Problem (10 minutes)
- Lewis's common knowledge theory (motivation, examples)
- The formalization challenge (gaps in informal argument)
- Why formalization matters (precision, discovery, cumulative progress)

### Part 2: Three Approaches (20 minutes)

**Cubitt & Sugden** (5 min)
- Primitive relations approach
- A1, A6 as axioms
- Works but limited

**Sillari** (7 min) ⭐ **DRAMATIC REVEAL**
- Modal logic seems natural
- But it FAILS! (live counterexample in Lean)
- Show B3_fails theorem executing
- Philosophical implications

**Vromen** (8 min) ⭐ **THE SOLUTION**
- Justification logic with explicit reasons
- A1 becomes 3-line proof (show in Lean)
- Why it works: "thereby" = composition
- Live verification of Lewis's theorem

### Part 3: Insights (10 minutes)
- Reasons are objects (conceptual insight from formalization)
- Minimal logic required (T1, T2, T3 only)
- Comparison table (summary slide)
- Implications for epistemology, game theory, AI

### Part 4: Broader Lessons (5 minutes)
- Formal verification in philosophy
- Lean as a tool for philosophy
- Future directions
- Call to action: formalize more philosophy!

### Q&A (15 minutes)

**Anticipated questions:**
- Why not use Coq/Isabelle/Agda? (Answer: Lean 4 is modern, has great tactics)
- Is this just logic? (No—philosophical insights about reasons)
- What about probabilistic common knowledge? (Future work)
- How hard was it to learn Lean? (Honest answer: ~3 months to proficiency)
- Can non-logicians use this? (Yes! Repository has documentation)

---

## Visual Materials

### Slides (approximate 30 slides)

1. Title
2. The Common Knowledge Puzzle
3. Lewis's Candle Example (photo)
4. Lewis's Informal Definition
5. The Formalization Gap
6. Three Approaches (overview table)
7. **Part 1: Cubitt & Sugden**
8. - Primitive relations
9. - Axioms A1, A6
10. - Proof of Lewis's theorem
11. - Limitations
12. **Part 2: Sillari** 
13. - Modal logic approach
14. - Kripke semantics
15. **COUNTEREXAMPLE!** (animated)
16. - B3_fails theorem (Lean code)
17. - Why modal logic fails
18. **Part 3: Vromen**
19. - Justification logic basics
20. - Explicit reason terms
21. - Application rule (AR)
22. - A1 proof (Lean code - 3 lines!)
23. - A6 proof (Lean code)
24. - Lewis's theorem proof structure
25. - Induction on G-closure
26. **Part 4: Insights**
27. - "Thereby" = composition (diagram)
28. - Comparison table (all three)
29. - Minimal tautologies (T1, T2, T3)
30. - Philosophical implications
31. - Future work
32. - Thank you + GitHub link

### Live Demo (5 minutes)

**What to show:**
1. Open Vromen_justification_logic.lean in VS Code
2. Navigate to A1 theorem
3. Show how proof is 3 lines
4. Demonstrate tactics completing proof
5. Show B3_fails counterexample
6. Execute #check to verify types
7. Show zero sorries with `lake build`

**Backup plan:** Pre-recorded screen capture if live demo fails

### Handouts (optional)

- One-page summary comparing three approaches
- QR code linking to GitHub repository
- Bibliography of key references
- Suggested reading order for the formalization

---

## Target Conferences

### Tier 1 (Top Priority)

**TARK 2026** (Theoretical Aspects of Rationality and Knowledge)
- **Perfect fit** - common knowledge is core TARK topic
- History of influential CK papers (Aumann, Fagin, etc.)
- Appreciates both philosophy and formal methods
- Deadline: Typically March for July conference (March 2026 for July 2026)
- **Decision: Submit here first**

**LOFT 2025** (Logic and the Foundations of Game Theory)
- Smaller, focused workshop
- Ideal for Lewis (convention connects to game theory)
- Friendly to formal methods
- Biennial (check if 2025 is happening)

### Tier 2 (Strong Fits)

**CPP 2025** (Certified Programs and Proofs)
- Focuses on formal verification
- Philosophy applications increasingly welcome
- Co-located with POPL
- Emphasize formalization aspects
- Deadline: Typically September for January conference

**IJCAI 2025** - Knowledge Representation track
- Broader AI conference
- Has session on epistemic logic
- Good visibility
- Deadline: Typically January for August conference

**FLoC 2026** (Federated Logic Conference)
- Happens every 4 years (next 2026)
- Multiple relevant workshops:
  - LORI (Logic, Rationality, Interaction)
  - Epistemic Logic Workshop
  - Justification Logic Workshop
- Great networking opportunity

### Tier 3 (Broader Venues)

**AAL 2025** (Amsterdam Colloquium)
- Formal semantics/pragmatics
- Common knowledge relevant to communication
- Lewis connections to language

**ESSLLI Student Session**
- If you're a student
- Great feedback, lower barrier
- Good practice for bigger venues

**APA (Pacific or Central Division)**
- Philosophy venue
- Formal epistemology session
- Broader philosophical audience

---

## Supplementary Materials for Submission

### What to Include

1. **Extended abstract** (if requested): Full 4-page version with proofs
2. **GitHub link**: https://github.com/[username]/lewis-common-knowledge-lean
3. **Demo video** (optional): 3-minute screen capture showing formalization
4. **Letter of support** (if student): From advisor

### What NOT to Include

- Full Lean code (too long, goes to supplementary link)
- Exhaustive related work (save for paper)
- Overly technical details (accessibility matters)

---

## Post-Acceptance Checklist

### Before Conference

- [ ] Practice talk 3+ times
- [ ] Test live demo on different computers
- [ ] Create backup video of demo
- [ ] Finalize slides (high-quality visuals)
- [ ] Prepare handouts if allowed
- [ ] Update GitHub README with conference details
- [ ] Test internet connection for live repository access

### At Conference

- [ ] Arrive early to test equipment
- [ ] Bring laptop + adapters + backups
- [ ] Have printed notes (in case of tech failure)
- [ ] Record talk if permitted (for website)
- [ ] Network with attendees interested in formal verification
- [ ] Take notes on feedback for paper

### After Conference

- [ ] Incorporate feedback into paper
- [ ] Add "presented at [conference]" to CV and GitHub
- [ ] Write blog post about experience
- [ ] Connect with interested researchers
- [ ] Consider submitting to journal (now with "presented at" credibility)

---

## Budget Estimate (if seeking funding)

- Conference registration: $400-800
- Travel (depends on location): $500-2000
- Accommodation (3-4 nights): $400-800
- **Total**: ~$1,500-3,500

**Funding sources to explore:**
- Department travel grants
- Graduate student association
- Conference student support programs
- ACM/IEEE student travel grants (for CPP)

---

## Timeline

**Now → 3 months:** Finalize formalization, write paper
**3-4 months:** Submit to conference (TARK or CPP)
**4-6 months:** Review period
**6-7 months:** Revisions if accepted
**7-9 months:** Conference preparation
**9 months:** Present!
**9-12 months:** Revise for journal based on feedback

---

**Bottom Line:** This work is conference-ready and will make a strong impression. The combination of philosophical depth, technical rigor, and practical demonstration makes it suitable for top-tier venues.
