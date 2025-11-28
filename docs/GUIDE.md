# Detailed Reading Guide

This guide helps you navigate the formalizations and understand the key concepts and proofs.

## For Philosophers

If you're primarily interested in the philosophical content:

1. **Start with the paper:** Read `pdfs/Vromen_-_2024_-_Reasoning_with_reasons_Lewis_on_common_knowledge.pdf` for the full philosophical argument.

2. **Then read the PDF versions** of the Lean files in this order:
   - `pdfs/cubitt_sugden_baseline.pdf` - Understand Lewis's argument
   - `pdfs/sillari_refutation.pdf` - See why modal logic fails
   - `pdfs/vromen_justification_logic.pdf` - The correct approach

The PDF files contain all the mathematical content with extensive natural language explanations.

## For Formal Methods Researchers

If you're interested in the Lean formalization techniques:

### Key Techniques Used

1. **Inductive Types for Transitive Closure** (`Sillari_refutation.lean`)
   ```lean
   inductive trcl (r : frame.World → frame.World → Prop) : 
     frame.World → frame.World → Prop
   | base {x y} : r x y → trcl r x y
   | step {x y z} : r x y → trcl r y z → trcl r x z
   ```

2. **Structural Induction** (`Cubitt_Sugden_baseline.lean`)
   ```lean
   inductive RC (φ : Prop) : Prop → Prop where
   | base : RC φ φ
   | step {u : Prop} (j : indiv) (hu : RC φ u) : RC φ (R j u)
   ```

3. **Explicit Terms in Logic** (`Vromen_justification_logic.lean`)
   ```lean
   def R (rb : reason → individual → Prop → Prop) (i : individual) (φ : Prop) : Prop :=
     ∃ r, rb r i φ
   ```

### Interesting Proofs

- **Counterexample construction** in `Sillari_refutation.lean` (B3_fails, C4_fails)
- **Complete hierarchy proof** in `Cubitt_Sugden_baseline.lean` (everyone_reason_of_rc)
- **Minimal axiom system** in `Vromen_justification_logic.lean` (AR, T1, T2, T3)

## Understanding the Three Approaches

### The Syntactic Approach (Cubitt-Sugden)

**Core definitions:** R and Ind are primitive (undefined) relations.

**Key axioms needed:**
```lean
axiom A1 : Ind A i p → R i A → R i p  -- Principle of detachment
axiom A6 : Ind A i (R j A) ∧ R i (Ind A j p) → Ind A i (R j p)  -- Propagation
```

**Advantage:** Makes everything explicit and provable.

**Disadvantage:** Cannot explain WHY A1 and A6 hold - they must be assumed.

### The Modal Logic Problem (Sillari)

**Core definition:**
```lean
def R (i : Agent) (φ : frame.World → Prop) : frame.World → Prop :=
  fun w => ∀ v, frame.rel i w v → φ v

def Ind (i : Agent) (φ ψ : frame.World → Prop) : frame.World → Prop :=
  fun w => R i φ w ∧ (φ w → ψ w)
```

**Problem:** This is just a conjunction - it cannot capture that the reason for ψ depends on the reason for φ (Lewis's "thereby").

**Result:** Axiom B3 (Lewis's A1) fails with explicit counterexample.

### The Justification Logic Solution (Vromen)

**Core definitions:**
```lean
def R (rb : reason → individual → Prop → Prop) (i : individual) (φ : Prop) : Prop :=
  ∃ r, rb r i φ  -- "i has A reason to believe φ"

def Ind (rb : reason → individual → Prop → Prop) (φ : Prop) (i : individual) (ψ : Prop) : Prop :=
  R rb i (φ → ψ)  -- "i has reason to believe the implication"
```

**Key axiom (Application Rule):**
```lean
axiom AR : rb s i (α → β) → rb t i α → rb (s * t) i β
```

The composite reason `s * t` explicitly contains both `s` and `t`, capturing Lewis's "thereby".

**Result:** A1 and A6 become 3-line and 10-line theorems respectively.

## Key Insights from the Formalizations

### 1. The "Thereby" Problem

Lewis says: "if i had reason to believe that A held, i would **thereby** have reason to believe that ___"

- Modal logic: Cannot capture this - reasons are implicit
- Primitive relations: Can state it but not explain it
- Justification logic: Captures it via reason composition (s * t)

### 2. Logical Omniscience

**Problem:** Should agents have reason to believe all tautologies?

- Modal logic (Sillari): YES - follows from necessitation rule
- Primitive relations (Cubitt-Sugden): YES - all valid inferences
- Justification logic (Vromen): NO - only three specific tautologies (T1, T2, T3)

### 3. Proof Strategy Differences

**Cubitt-Sugden:** Syntactic proof showing pattern for first 4 levels
- Extension: Full inductive proof for infinite hierarchy

**Sillari:** Semantic proof via reachability in Kripke frames
- Problem: Either incorrect or trivial

**Vromen:** Structural induction on G-closure
- Key lemma: Indication propagates through entire closure
- Then apply A1 to convert indication to reason

## Common Questions

### Q: Why three approaches?

**A:** Each reveals something important:
- Cubitt-Sugden shows the STRUCTURE of Lewis's argument
- Sillari shows what DOESN'T work
- Vromen shows the CORRECT FOUNDATION

### Q: Is justification logic necessary?

**A:** For Lewis's specific theory, yes. The "thereby" in his definition of indication requires tracking evidential dependence, which requires explicit reason terms.

### Q: What about actual beliefs (not just reasons)?

**A:** The formalization focuses on reasons to believe because:
1. That's the foundation of Lewis's theory
2. Actual beliefs depend on rationality (different issue)
3. See Section 5 of the paper for discussion

## Next Steps

### For Further Reading

1. **Lewis (1969)** - Original source (Convention: A Philosophical Study)
2. **Cubitt & Sugden (2014)** - Extended analysis of common reasoning
3. **Artemov & Fitting (2019)** - Comprehensive justification logic text

### For Extension

Possible directions:
- Add semantics for justification logic
- Formalize Lewis's account of actual beliefs
- Apply to specific coordination games
- Extend to probabilistic reasons

### For Questions

- Open an issue on GitHub
- Email: hjvromen@icloud.com
- Cite the paper and this repository in your work

---

**Remember:** All proofs are fully verified. You can trust every `theorem` and `lemma` - Lean checked them!
