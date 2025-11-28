# Project Summary: Formalizing Lewis's Common Knowledge

## Motivation

This project arose from a fundamental question in philosophy and game theory: **How can we have common knowledge?**

Common knowledge seems essential for coordination and communication, yet also seems impossible because it requires an infinite regress of beliefs about beliefs about beliefs...

David Lewis (1969) offered a distinctive solution based on "reasons to believe" rather than mental states. But his argument was informal and had gaps. This project completes his argument using modern proof assistants.

## The Three Approaches

### Approach 1: Primitive Relations (Cubitt-Sugden 2003)

**Idea:** Treat R and Ind as undefined primitive relations

**Axioms needed:**
```
A1: Ind A i p → R i A → R i p
A6: Ind A i (R j A) ∧ R i (Ind A j p) → Ind A i (R j p)
```

**Result:** ✓ Works, but incomplete
- Lewis's theorem provable
- All assumptions explicit
- Cannot explain WHY A1 and A6 hold

**Lesson:** Shows the structure of Lewis's argument

### Approach 2: Modal Logic (Sillari 2005)

**Idea:** Use Kripke semantics with □ operators

**Definition of indication:**
```
Ind i φ ψ := □i φ ∧ (φ → ψ)
```

**Result:** ❌ FAILS
- Lewis's axiom A1 has counterexamples
- Lewis's theorem either false or trivial
- Root problem: Cannot capture "thereby" with conjunction

**Lesson:** Modal logic is the wrong framework

### Approach 3: Justification Logic (Vromen 2024)

**Idea:** Reasons are objects that can be composed

**Definitions:**
```
R i φ := ∃r. r :i φ                  (i has a reason to believe φ)
Ind A i φ := R i (A → φ)              (i has reason for the implication)
```

**Application rule:**
```
s :i (α → β),  t :i α  ⊢  (s * t) :i β
```

**Result:** ✓✓ Complete solution
- A1 proven in 3 lines
- A6 proven in 10 lines  
- Lewis's theorem proven by induction
- Only 3 tautologies needed (no logical omniscience)

**Lesson:** Justification logic is the right framework

## Key Technical Insights

### 1. The "Thereby" Problem

Lewis: "if i had reason to believe that A held, i would **thereby** have reason to believe that ___"

The word "thereby" indicates evidential dependence - the reason for the conclusion must depend on the reason for the premise.

**Modal logic:** Cannot express this (reasons are implicit)

**Justification logic:** The composite reason `s * t` explicitly contains `t`, capturing the dependence.

### 2. Structural vs. Semantic Approaches

**Cubitt-Sugden:** Syntactic approach with inference rules
- Advantage: Makes evidential structure explicit
- Problem: Must assume what should be proven

**Sillari:** Semantic approach via Kripke frames
- Problem: Truth conditions don't preserve evidential structure

**Vromen:** Structural approach with explicit terms
- Reasons have algebraic structure (multiplication)
- Evidential dependence encoded in term structure
- Properties follow from structure

### 3. Minimal Rationality

How much logical power do agents need?

**Cubitt-Sugden:** All valid inferences (logical omniscience)
**Modal logic:** All tautologies (logical omniscience)
**Justification logic:** Only three specific inferences:
- T1: Conjunction formation (α, β ⊢ α ∧ β)
- T2: Transitivity (α→β, β→γ ⊢ α→γ)  
- T3: Theory of mind (reasoning about others' reasoning)

These correspond to reasoning patterns humans find natural.

## Proof Architecture

All three files follow the same overall structure:

1. **Definitions** - Core concepts (R, Ind, CRB/CK)
2. **Axioms** - What must be assumed
3. **Derived rules** - What follows from axioms
4. **Main theorem** - Lewis's result

But they differ in what goes where:

|     | Sillari        | Cubitt-Sugden | Vromen                 |
| --- | -------------- | ------------- | ---------------------- |
| R   | Modal operator | Primitive     | Existential (∃r. r:iφ) |
| Ind | R ∧ →          | Primitive     | R(A→φ)                 |
| A1  | ❌ Fails        | Axiom         | Theorem                |
| A6  | N/A            | Axiom         | Theorem                |

## Future Directions

### Immediate Extensions
- Add soundness/completeness proofs for justification logic
- Formalize Lewis's Chapter 5 (actual beliefs from reasons)

## Pedagogical Value

This formalization serves as:

1. **Case study in formal philosophy** - Shows how proof assistants help philosophy
2. **Introduction to justification logic** - Concrete application domain
3. **Example of comparative formalization** - Three approaches to same problem
4. **Model for rigorous philosophy** - Every claim is machine-verified

## Why This Matters

### For Philosophy
- Resolves 55-year-old gap in Lewis's argument
- Demonstrates value of formal methods in philosophy
- Shows how logical framework choice affects results

### For Logic
- Novel application of justification logic
- Demonstrates superiority over modal logic for this problem
- Minimal axiomatization with maximal results

## Verification Statistics

- **Total lines of Lean code:** ~1,500
- **Number of theorems/lemmas:** 40+
- **Number of `sorry` statements:** 0 (complete!)
- **Dependencies:** Mathlib only
- **Build time:** ~2 minutes

## Resources

### Essential Reading
1. Lewis (1969) - Original source
2. Vromen (2024) - This paper
3. Artemov & Fitting (2019) - Justification logic textbook

### Learning Lean 4
- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)

## Acknowledgments

This work builds on:
- David Lewis's original insight (1969)
- Cubitt and Sugden's clarification (2003)
- Sillari's modal logic attempt (2005)
- Artemov's justification logic (2006+)

And benefits from:
- Mathlib's extensive libraries
- Lean 4's powerful proof assistant
- Feedback from anonymous reviewers

