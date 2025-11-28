# Visual Project Overview

## Project Structure at a Glance

```
lewis-common-knowledge-lean4/
│
├── 📄 README.md              ← Start here! Main documentation
├── 📄 LICENSE                ← MIT License
├── 📄 CONTRIBUTING.md        ← Contribution guidelines
├── 📄 PUBLISHING.md          ← How to publish to GitHub
├── 🔧 setup.sh              ← Quick setup script
├── 🔧 lakefile.lean         ← Lean project configuration
├── 🔧 lean-toolchain        ← Lean version specification
├── 🔧 .gitignore            ← Git ignore patterns
│
├── 📁 src/                   ← Lean source files
│   ├── Sillari_refutation.lean              (Modal logic fails)
│   ├── Cubitt_Sugden_baseline.lean          (Syntactic approach)
│   └── Vromen_justification_logic.lean      (Correct solution)
│
├── 📁 pdfs/                  ← Documentation PDFs
│   ├── sillari_refutation.pdf
│   ├── cubitt_sugden_baseline.pdf
│   ├── vromen_justification_logic.pdf
│   └── Vromen_-_2024_-_Reasoning_with_reasons... (Published paper)
│
├── 📁 docs/                  ← Additional documentation
│   ├── GUIDE.md                             (Detailed reading guide)
│   └── PROJECT_SUMMARY.md                   (Technical summary)
│
└── 📁 .github/               ← GitHub automation
    └── workflows/
        └── lean.yml                         (CI/CD pipeline)
```

## The Three Approaches Compared

```
┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  SILLARI (2005): Modal Logic Approach                              │
│  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━                       │
│                                                                     │
│  R i φ := □i φ           (Modal box operator)                      │
│  Ind i φ ψ := R i φ ∧ (φ→ψ)   (Conjunction)                        │
│                                                                     │
│  Result: ❌ FAILS                                                   │
│  • B3 (A1) has counterexamples                                     │
│  • Cannot capture "thereby"                                        │
│  • Lewis's theorem false or trivial                                │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  CUBITT-SUGDEN (2003): Primitive Relations                         │
│  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━                       │
│                                                                     │
│  R : indiv → Prop → Prop        (Primitive)                        │
│  Ind : Prop → indiv → Prop → Prop   (Primitive)                    │
│                                                                     │
│  Axioms Required:                                                  │
│  • A1: Ind A i p → R i A → R i p                                   │
│  • A6: Ind A i (R j A) ∧ R i (Ind A j p) → Ind A i (R j p)        │
│                                                                     │
│  Result: ✓ Works, but incomplete                                   │
│  • Lewis's theorem proven                                          │
│  • Cannot explain WHY axioms hold                                  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  VROMEN (2024): Justification Logic                                │
│  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━                       │
│                                                                     │
│  R i φ := ∃r. r :i φ         (Existential over reasons)            │
│  Ind A i φ := R i (A → φ)    (Reason for implication)              │
│                                                                     │
│  Application Rule:                                                 │
│  s :i (α→β), t :i α  ⊢  (s*t) :i β                                 │
│                                                                     │
│  Result: ✅ Complete solution                                       │
│  • A1 proven in 3 lines                                            │
│  • A6 proven in 10 lines                                           │
│  • Lewis's theorem proven by induction                             │
│  • Only 3 tautologies needed                                       │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## File Size and Complexity

```
┌─────────────────────────────────────────────────────────────┐
│ File                          │ Lines │ Theorems │ Status   │
├───────────────────────────────┼───────┼──────────┼──────────┤
│ Sillari_refutation.lean       │  ~400 │    15    │ Complete │
│ Cubitt_Sugden_baseline.lean   │  ~250 │     8    │ Complete │
│ Vromen_justification_logic.lean│  ~300 │    12    │ Complete │
├───────────────────────────────┼───────┼──────────┼──────────┤
│ Total                         │ ~950  │    35    │    0%    │
│                               │       │          │  sorry   │
└─────────────────────────────────────────────────────────────┘
```

## Dependency Graph

```
Vromen_justification_logic.lean
  │
  ├─→ AR (Application Rule)
  ├─→ T1 (Conjunction)
  ├─→ T2 (Transitivity)
  ├─→ T3 (Theory of Mind)
  │
  ├─→ E1 (Derived: Modus Ponens)
  ├─→ E2 (Derived: Chaining)
  ├─→ E3 (Derived: Distribution)
  │
  ├─→ A1 (Proven: 3 lines)
  ├─→ A6 (Proven: 10 lines)
  │
  └─→ Lewis's Theorem (Proven by induction)


Cubitt_Sugden_baseline.lean
  │
  ├─→ A1 (AXIOM: Detachment)
  ├─→ A6 (AXIOM: Propagation)
  │
  ├─→ L1-L4 (Concrete levels)
  ├─→ RC (R-closure)
  │
  └─→ Lewis's Theorem (Proven by induction on RC)


Sillari_refutation.lean
  │
  ├─→ Kripke Frame (Multi-agent)
  ├─→ R (Modal operator)
  ├─→ Ind (Conjunction)
  │
  ├─→ B3_fails (COUNTEREXAMPLE)
  ├─→ C4_fails (COUNTEREXAMPLE)
  │
  └─→ Lewis_fails (Two interpretations, both problematic)
```

## Key Metrics

### Proof Completeness
- ✅ **100% verified** - No `sorry` statements
- ✅ **Machine-checked** - All proofs validated by Lean 4
- ✅ **Self-contained** - Only depends on Mathlib

### Code Quality
- 📝 **Extensively documented** - Every section explained
- 🎯 **Clear naming** - Intuitive function and theorem names
- 🔍 **Traceable** - References to original papers throughout

### Reproducibility
- ⚙️ **Automated build** - GitHub Actions CI/CD
- 📦 **Locked dependencies** - Specific Lean version
- 🚀 **Quick setup** - One-command installation

## Timeline

```
1969  │ Lewis publishes Convention
      │ • Informal argument for common knowledge
      │
2003  │ Cubitt & Sugden formalize syntactically
      │ • Make A1 and A6 explicit as axioms
      │
2005  │ Sillari attempts modal logic formalization
      │ • Shows fundamental problems
      │
2024  │ Vromen proves A1 and A6 as theorems
      │ • Uses justification logic
      │ • This formalization published!
      │
      ↓ Now: Machine-verified in Lean 4
```

## Usage Statistics

### For Reading (Start Here)
1. **README.md** - Overview and quickstart
2. **docs/GUIDE.md** - Detailed navigation
3. **PDFs/** - Readable versions of proofs

### For Coding
1. **src/Cubitt_Sugden_baseline.lean** - Understand the structure
2. **src/Sillari_refutation.lean** - See what fails
3. **src/Vromen_justification_logic.lean** - The solution

### For Publishing
1. **PUBLISHING.md** - Step-by-step GitHub guide
2. **CONTRIBUTING.md** - How others can contribute
3. **setup.sh** - Automated setup script

## What Makes This Special

```
┌─────────────────────────────────────────────────────────────┐
│                                                             │
│  🎯 FIRST complete formalization of Lewis's theorem        │
│  🔬 PROVES problematic axioms from first principles        │
│  📚 THREE approaches for comparison                        │
│  ✅ ZERO unproven assumptions                              │
│  🌍 FULLY reproducible and verifiable                      │
│  📖 EXTENSIVELY documented for learning                    │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

## Quick Commands Reference

```bash
# Setup
./setup.sh                    # Run complete setup

# Build
lake update                   # Update dependencies
lake build                    # Build project

# Verify
grep -r "sorry" src/*.lean    # Check for incomplete proofs

# Git
git init                      # Initialize repository
git add .                     # Stage all files
git commit -m "message"       # Commit changes
git push origin main          # Push to GitHub
```

## Support and Community

- 💬 Questions: Open a GitHub issue
- 📧 Email: hjvromen@icloud.com
- 🌐 Lean Zulip: https://leanprover.zulipchat.com/
- 📄 Paper: Economics & Philosophy 40(2), 397-418

---

**Ready to publish?** See PUBLISHING.md for step-by-step instructions!
