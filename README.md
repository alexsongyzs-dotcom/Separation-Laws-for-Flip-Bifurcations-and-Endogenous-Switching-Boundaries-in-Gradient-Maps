# Paper 04: Separation Laws for Flip Bifurcations and Endogenous Switching Boundaries in Gradient Maps

This repository contains the LaTeX source code for the paper

> *Separation Laws for Flip Bifurcations and Endogenous Switching Boundaries in Gradient Maps*

and a **fully machine‑verified Lean 4 formalization** of all key theorems (68 theorems/lemmas, no `sorry`, no `axiom`, `lake build` passes completely).

## Repository Structure

```
.
├── paper/                      # LaTeX source (main.tex, chapters, references.bib, main.pdf)
└── lean-proofs/                # Lean 4 formalization (Lean 4.33.1 + mathlib4 v4.33.1)
    ├── Lean4Proofs/            # 8 Lean proof files
    ├── lakefile.lean
    ├── lean-toolchain
    └── TheoremsMapping.md      # Mapping from paper propositions to Lean theorems
```

## Lean Formalization

- **Environment**: Lean 4.33.1 with mathlib4 v4.33.1 (see `lean-proofs/lean-toolchain`)
- **Scope**: Clipping operators, exact gradient balance, simultaneous switching contact, universal unit multiplier, planar model separation coefficients \(K_2 = 2b/\lambda^4\) and \(K_4 = 6b^2/\lambda^7 - 2d/\lambda^6\), etc.
- **Correspondence**: A detailed theorem‑to‑theorem mapping is available at `lean-proofs/TheoremsMapping.md`.

### Verification

```bash
cd lean-proofs
lake update          # fetch mathlib and dependencies
lake exe cache get   # download precompiled mathlib olean cache
lake build           # compile and verify all proofs
```

To build the paper PDF:

```bash
cd paper
pdflatex main.tex && bibtex main && pdflatex main.tex && pdflatex main.tex
```
