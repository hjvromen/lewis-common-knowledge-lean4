# Contributing to Lewis Common Knowledge Formalizations

Thank you for your interest in contributing! This project welcomes contributions from philosophers, mathematicians, and formal verification enthusiasts.

## Ways to Contribute

### 1. Report Issues
- Found a typo or unclear explanation? Open an issue!
- Have questions about the proofs? Ask in an issue!
- Spotted a potential improvement? Suggest it!

### 2. Improve Documentation
- Add more examples or intuitive explanations
- Improve comments in the Lean code
- Write tutorials or blog posts about the formalization
- Translate documentation to other languages

### 3. Extend the Formalizations
- Add semantics for the justification logic approach
- Formalize Lewis's account of actual beliefs (Chapter 5)
- Connect to specific game-theoretic applications
- Prove additional properties or lemmas

### 4. Code Improvements
- Refactor proofs for clarity or brevity
- Add automation with custom tactics
- Improve naming conventions
- Add more examples

## Guidelines

### For Issue Reports
- Use a clear, descriptive title
- Provide context: which file, which theorem/lemma
- Include the Lean version you're using
- If it's a proof issue, show what you tried

### For Pull Requests

1. **Before starting major work:** Open an issue to discuss your idea

2. **Code style:**
   - Follow existing naming conventions
   - Add docstrings for new definitions and theorems
   - Include comments explaining non-obvious proof steps
   - Use descriptive variable names

3. **Documentation:**
   - Update README.md if you add new features
   - Add comments explaining your contribution
   - If you prove new theorems, explain their significance

4. **Testing:**
   - Ensure `lake build` completes without errors
   - No `sorry` statements unless explicitly noted as future work
   - Check that your changes don't break existing proofs

5. **Commit messages:**
   - Use clear, descriptive commit messages
   - Reference issue numbers when applicable
   - Example: "Add semantics for justification logic (fixes #42)"

### Coding Standards

#### Lean Code
```lean
-- Good: Clear theorem statement with docstring
/-- Lewis's axiom A1 follows from the application rule.
    This 3-line proof shows justification logic is the right framework. -/
theorem A1 : Ind rb A i α → R rb i A → R rb i α := by
  intro h1 h2
  exact E1 h1 h2

-- Less good: No explanation
theorem A1 : Ind rb A i α → R rb i A → R rb i α := by
  intro h1 h2; exact E1 h1 h2
```

#### Documentation
- Use complete sentences
- Explain the intuition before the formalism
- Provide examples when possible
- Link to relevant literature

## Development Setup

1. Install Lean 4 and elan:
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

2. Clone the repository:
```bash
git clone https://github.com/yourusername/lewis-common-knowledge-lean4.git
cd lewis-common-knowledge-lean4
```

3. Build the project:
```bash
lake update
lake build
```

4. Open in VS Code with Lean extension:
```bash
code .
```

## What Makes a Good Contribution?

### Especially Welcome:
- Connections to other formalizations (game theory, modal logic, etc.)
- Alternative proofs that are more intuitive or elegant
- Examples demonstrating the theory applied to concrete scenarios
- Educational materials for learning the formalization

### Please Avoid:
- Changing the core results without strong justification
- Adding `sorry` without a plan to remove them
- Breaking existing proofs
- Reformatting large sections without functional changes

## Attribution

Contributors will be acknowledged in:
- The repository README.md
- Commit history
- Future papers that build on this work (where appropriate)

## Questions?

- Open an issue for questions about the formalization
- Email hjvromen@icloud.com for other inquiries
- Cite the paper: Vromen (2024) in Economics & Philosophy

## Code of Conduct

This project follows standard academic discourse principles:
- Be respectful and constructive
- Focus on ideas, not individuals  
- Welcome newcomers and help them learn
- Give credit where credit is due

Thank you for contributing to formal philosophy!
