# Lean 4 Formalization of Paper_04

Machine-verified Lean 4 proofs of all key theorems of the paper
*Separation Laws for Flip Bifurcations and Endogenous Switching Boundaries
in Gradient Maps*.

**Verification status: 68 theorems/lemmas, `lake build` passes, no `sorry`, no `axiom`.**
(Lean 4.33.1 + mathlib4 v4.33.1)

## Reproduction

Prerequisites: Lean 4 (installed via elan) + Git.

    cd lean-proofs
    lake update          # fetch mathlib4 v4.33.1 and dependencies
    lake exe cache get   # download precompiled olean cache (~1 GB)
    lake build           # verify all proofs

## Contents

| File | Content | Paper section |
|---|---|---|
| Lean4Proofs/Clipping.lean | Clipping operator identities | §2 |
| Lean4Proofs/GradientBalance.lean | Exact gradient balance, midpoint–half-difference equations | §5 |
| Lean4Proofs/GradientBalance2.lean | Simultaneous contact, no mixed two-cycle, fully clipped geometry | §5–§7 |
| Lean4Proofs/Spectrum.lean | Spectral consequences and flip threshold | §2, §4 |
| Lean4Proofs/NormalForm.lean | Normal-form second iterate and amplitude algebra | §4 |
| Lean4Proofs/UnitMultiplier.lean | Universal unit multiplier | §7 |
| Lean4Proofs/PlanarModel.lean | Planar model and separation-coefficient extraction | §8 |
| Lean4Proofs/Proofs.lean | Main entry point | — |

## Notes

1. For §7, `ClippingStructure` bundles two analytic axioms — Euler's identity and the
   oddness of the norm derivative, valid for any C¹ positively homogeneous norm — while
   all remaining conclusions are machine-proved.
2. Asymptotic statements in §4–§6 (O(·) expansions, center manifolds, implicit-function
   branches) are formalized as exact algebraic kernels; e.g., the two-step multiplier is
   verified to be exactly (1 − 2λμ)².
