# Formalizing Lewis's Theory of Common Knowledge in Lean 4

[![DOI](https://zenodo.org/badge/1105929111.svg)](https://doi.org/10.5281/zenodo.17759320)

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Lean 4](https://img.shields.io/badge/Lean-4.26.0--rc2-blue.svg)](https://leanprover.github.io/lean4/doc/)

[![Build Status](https://github.com/hjvromen/lewis-common-knowledge-lean4/actions/workflows/lean.yml/badge.svg)](https://github.com/hjvromen/lewis-common-knowledge-lean4/actions)

This repository contains machine-verified formalizations of three approaches to David Lewis's theory of common knowledge, fully implemented in Lean 4. The project builds on the paper:

**Vromen, H. (2024). Reasoning with reasons: Lewis on common knowledge. *Economics & Philosophy*, 40(2), 397–418.** 
[DOI: 10.1017/S0266267123000238](https://doi.org/10.1017/S0266267123000238)

## Overview

David Lewis (1969) introduced a distinctive account of common knowledge based on "reasons to believe" rather than knowledge or belief as mental states. This project provides three complete formalizations:

1. **Cubitt-Sugden Baseline** - Syntactic approach with primitive operators
2. **Sillari's Modal Logic Approach** - Demonstrates fundamental limitations
3. **Vromen's Justification Logic** - Novel solution using explicit reason terms

All proofs are fully formalized and verified in Lean 4 with **zero `sorry` statements**.

## Key Results

| Approach | A1 Status | A6 Status | Lewis's Theorem | Limitations |
|----------|-----------|-----------|-----------------|-------------|
| **Cubitt-Sugden** | AXIOM | AXIOM | ✓ Proven | Must assume A1 and A6 |
| **Sillari** | ❌ FAILS | N/A | False/Trivial | Modal logic cannot capture "thereby" |
| **Vromen** | ✅ THEOREM | ✅ THEOREM | ✓ Proven | Minimal assumptions, no logical omniscience |

## Repository Structure

```
.
├── README.md                          # This file
├── LICENSE                            # MIT License
├── CONTRIBUTING                       # Way to contribute
├── setup.sh                           # Setup instructions
├── .gitignore                         # Files and folders excluded
├── lake-manifest.json                 # Locked dependency versions
├── lean-toolchain                     # Lean version specification
├── Lewis.lean                         # Library root file (required by Lake)
├── Cubitt_Sugden_baseline.lean        # Syntactic reconstruction
├── Sillari_refutation.lean            # Modal logic counterexamples
├── Vromen_justification_logic.lean    # Justification logic solution
├── pdfs/
│   ├── sillari_refutation.pdf         # PDF version of the Lean file
│   ├── cubitt_sugden_baseline.pdf     # PDF version of the Lean file
│   ├── vromen_justification_logic.pdf # PDF version of the Lean file
│   └── Vromen_-_2024_-_Reasoning_with_reasons_Lewis_on_common_knowledge.pdf
└── docs/
    ├── GUIDE.md                       # Detailed reading guide
    ├── PROJECT_SUMMARY.md             # Technical overview

```

## Quick Start

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) (version 4.0.0 or later)
- [elan](https://github.com/leanprover/elan) (Lean version manager)

### Installation

```bash
# Clone the repository
git clone https://github.com/hjvromen/lewis-common-knowledge-lean4.git
cd lewis-common-knowledge-lean4

# Install dependencies
lake update
lake build
```

### Exploring the Formalizations

Each Lean file is extensively documented with:
- Mathematical explanations of key concepts
- Step-by-step proof developments
- Comparison with other approaches
- References to Lewis's original text

**Recommended reading order:**

1. Start with `Cubitt_Sugden_baseline.lean` to understand Lewis's argument structure
2. Read `Sillari_refutation.lean` to see why modal logic fails
3. Study `Vromen_justification_logic.lean` for the correct foundation

Alternatively, read the PDF versions in the `pdfs/` directory for rendered documentation.

## Main Contributions

### 1. Cubitt-Sugden Baseline (`Cubitt_Sugden_baseline.lean`)

Formalizes Cubitt and Sugden's (2003) syntactic reconstruction:

- Treats "reason to believe" (R) and "indication" (Ind) as primitive relations
- Proves Lewis's theorem for the complete infinite hierarchy (extends beyond their paper)
- Makes all assumptions explicit as axioms
- Clean axiomatic foundation but cannot explain why A1 and A6 hold

### 2. Sillari Refutation (`Sillari_refutation.lean`)

Demonstrates that Sillari's (2005) modal logic approach has fundamental flaws:

- **B3 (Lewis's A1) fails** - Machine-verified counterexample
- **C4 (Cubitt-Sugden axiom) fails** - Machine-verified counterexample  
- **Lewis's theorem fails** - Under local assumptions (counterexamples with 1 and 2 agents)
- **Lewis's theorem is trivial** - Under global assumptions

**Root problem:** Modal logic's box operator (□) cannot capture Lewis's "thereby" - the evidential dependence between reasons.

### 3. Vromen's Justification Logic (`Vromen_justification_logic.lean`)

Novel formalization using explicit reason terms:

- **A1 proven as theorem** - 3 lines from application rule (AR)
- **A6 proven as theorem** - 10 lines from E2, E3  
- **Lewis's theorem proven** - Non-trivial structural induction
- **No logical omniscience** - Only three tautologies (T1, T2, T3) needed
- **Captures "thereby"** - Reason composition via multiplication operator

**Key insight:** `Ind A i φ := R i (A → φ)` where `R i ψ := ∃r. r :i ψ`

The composite reason `s * t` explicitly contains both `s` and `t`, capturing evidential dependence.

## Technical Highlights

The formalizations use:
- Mathlib tactics for automation
- Inductive types for transitive closure
- Custom relation definitions
- Structural induction for completeness proofs

The justification logic approach introduces:
- Multiplicative structure on reasons (`s * t`)
- Application rule for reason composition
- Minimal reason constants (conjConst, transConst, distConst)

## Citation

If you use this formalization in your research, please cite:

```bibtex
@article{vromen2024,
  title={Reasoning with reasons: Lewis on common knowledge},
  author={Vromen, Huub},
  journal={Economics \& Philosophy},
  volume={40},
  number={2},
  pages={397--418},
  year={2024},
  publisher={Cambridge University Press},
  doi={10.1017/S0266267123000238}
}

@software{vromen2025lean,
  title={Formalizing Lewis's Theory of Common Knowledge in Lean 4},
  author={Vromen, Huub},
  year={2025},
  doi={10.5281/zenodo.17759320},
  url={https://github.com/hjvromen/lewis-common-knowledge-lean4},
}
```

## References

- **Lewis, D.** (1969). *Convention: A Philosophical Study*. Cambridge, MA: Harvard University Press.
- **Cubitt, R. P., & Sugden, R.** (2003). Common knowledge, salience and convention: A reconstruction of David Lewis' game theory. *Economics and Philosophy*, 19, 175–210.
- **Sillari, G.** (2005). A logical framework for convention. *Synthese*, 147, 379–400.
- **Vromen, H.** (2024). Reasoning with reasons: Lewis on common knowledge. *Economics & Philosophy*, 40(2), 397–418.
- **Artemov, S., & Fitting, M.** (2019). *Justification Logic: Reasoning with Reasons*. Cambridge University Press.

## Contributing

Contributions are welcome! Please feel free to:
- Open issues for bugs or questions
- Submit pull requests for improvements
- Suggest extensions or additional formalizations

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Author

**Huub Vromen**  
Department of Philosophy  
Radboud University, Nijmegen, Netherlands  
Email: hjvromen@icloud.com

## Acknowledgments

The project uses [Mathlib](https://github.com/leanprover-community/mathlib4) extensively.

---

**Note:** This is a complete, verified formalization with no unproven assumptions (`sorry` statements). All three approaches are fully machine-checked by Lean 4's proof assistant.
