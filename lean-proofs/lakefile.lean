import Lake
open Lake DSL

package «Lean4Proofs» where
  -- Formal statements and machine-checked proofs for Paper_04

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

@[default_target]
lean_lib «Lean4Proofs» where
  roots := #[`Lean4Proofs.Proofs]
