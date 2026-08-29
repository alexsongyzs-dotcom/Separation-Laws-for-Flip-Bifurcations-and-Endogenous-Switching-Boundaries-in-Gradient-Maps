import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic

/-!
# Universal unit multiplier for fully clipped period-two orbits  (Paper_04, §6)

The paper's Section 6 rests on two *analytic* facts about the clipping norm
`ρ = ‖·‖⋄` (H5: `ρ` is `C³` away from the origin, positively homogeneous):

  1. Euler's identity `Dρ(u)[u] = ρ(u) = 1` on the unit sphere
     (paper eq. (6.7));
  2. oddness of the derivative of the even function `ρ`:
     `Dρ(-u) = -Dρ(u)` (paper remark after eq. (6.12)).

We bundle these two facts in the structure `ClippingStructure`.  Everything
after them — the projection `P_u = I - u ⊗ φ_u`, annihilation of the radial
covector, pointwise neutrality `φ_u DF(x) = φ_u` (Prop. 6.5), and the
universal unit multiplier of the two-step monodromy (Thm. 6.1) — is
machine-checked below.

The eigenvalue-1 conclusion uses only finite-dimensionality
(`Module.Finite ℝ E`) and the rank–nullity theorem.
-/

/-- The analytic input from the geometry of the clipping norm (H5). -/
structure ClippingStructure (E : Type*) [AddCommGroup E] [Module ℝ E] where
  /-- The norm `ρ`.  We only use its evenness and unit-sphere geometry. -/
  rho : E → ℝ
  /-- The derivative covector at unit vectors: `φ_u := Dρ(u)`. -/
  phi : E → E →ₗ[ℝ] ℝ
  /-- Euler's identity: `Dρ(u)[u] = ρ(u) = 1` on the unit sphere (eq. (6.7)). -/
  euler : ∀ ⦃u : E⦄, rho u = 1 → phi u u = 1
  /-- The norm is even: `ρ(-g) = ρ(g)`. -/
  even : ∀ g : E, rho (-g) = rho g
  /-- Oddness of the derivative: `φ_{-u} = -φ_u` (paper §6.4, remark). -/
  deriv_odd : ∀ u : E, phi (-u) = -phi u

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (CS : ClippingStructure E)

/-- The radial clipping derivative (paper eq. (6.10)):

    DC_c(g) = (c/ρ(g)) (I - u ⊗ φ_u),    u = g/ρ(g),  φ_u = Dρ(u).

We treat it as an abstract linear map parameterized by the direction `u`,
the covector `φ`, and the scaling `c/r`. -/
noncomputable def clipDeriv (c r : ℝ) (u : E) (φ : E →ₗ[ℝ] ℝ) : E →ₗ[ℝ] E :=
  (c / r) • ((1 : E →ₗ[ℝ] E) - φ.smulRight u)

/-- `P_u := I - u ⊗ φ_u` annihilates the radial direction: `P_u u = 0`
(paper eq. (6.12)). -/
lemma proj_u_annihilates_u {u : E} (hu : CS.rho u = 1) :
    ((1 : E →ₗ[ℝ] E) - (CS.phi u).smulRight u) u = 0 := by
  simp [CS.euler hu]

/-- `φ_u (P_u h) = 0`: the projection kills the radial covector. -/
lemma phi_annihilates_proj {u h : E} (hu : CS.rho u = 1) :
    CS.phi u (((1 : E →ₗ[ℝ] E) - (CS.phi u).smulRight u) h) = 0 := by
  simp [CS.euler hu]

/-- The radial covector is annihilated by the clipping derivative:
`φ_u (DC_c(g) h) = 0` for all `h` (paper eq. (6.16)). -/
lemma clipDeriv_annihilates {c r : ℝ} {u : E} (hu : CS.rho u = 1) :
    ∀ h : E, CS.phi u (clipDeriv c r u (CS.phi u) h) = 0 := by
  intro h
  simp [clipDeriv, CS.euler hu]

/-- The model of `DF_{η,c}(x)` in the strictly clipped region (eq. (6.17)):

    DF(x) = I - η (DC_c(∇V x) ∘ D²V(x)).

`H` plays the role of `D²V(x)`. -/
noncomputable def clippedJacobian (η c r : ℝ) (u : E) (H : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  (1 : E →ₗ[ℝ] E) - η • (clipDeriv c r u (CS.phi u) ∘ₗ H)

/-- Proposition 6.5 (pointwise neutral covector): `φ_u DF_{η,c}(x) = φ_u`
for `x ∈ Ω_c⁺` (eq. (6.18)). -/
theorem pointwise_neutral {η c r : ℝ} {u : E} (hu : CS.rho u = 1) (H : E →ₗ[ℝ] E) :
    CS.phi u ∘ₗ clippedJacobian CS η c r u H = CS.phi u := by
  ext h
  unfold clippedJacobian
  simp [clipDeriv_annihilates CS hu]

/-- The two-step monodromy of a fully clipped two-cycle:
`M = DF(y₋) ∘ DF(y₊)` (eq. (6.19)). -/
noncomputable def monodromy (A B : E →ₗ[ℝ] E) : E →ₗ[ℝ] E := B ∘ₗ A

/-- Theorem 6.1 (universal unit multiplier, left-covector form, eq. (6.22)):

if the two points of a fully clipped two-cycle have opposite gradient
directions `±u` (guaranteed by Prop. 6.1), then the same covector `φ_u`
is a left eigenvector of the monodromy:  `φ_u M = φ_u`. -/
theorem universal_unit_multiplier_left {A B : E →ₗ[ℝ] E} {u : E}
    (hu : CS.rho u = 1)
    (hA : CS.phi u ∘ₗ A = CS.phi u)
    (hB : CS.phi (-u) ∘ₗ B = CS.phi (-u)) :
    CS.phi u ∘ₗ monodromy A B = CS.phi u := by
  have hneg : CS.phi (-u) = -CS.phi u := CS.deriv_odd u
  -- from hB : φ_{-u} B = φ_{-u}  and  φ_{-u} = -φ_u  we get  φ_u B = φ_u
  have hB' : CS.phi u ∘ₗ B = CS.phi u := by
    rw [hneg] at hB
    have hB'' : -(CS.phi u ∘ₗ B) = -CS.phi u := by
      -- (-φ_u) ∘ₗ B = -(φ_u ∘ₗ B)
      simpa [LinearMap.neg_comp] using hB
    exact neg_injective hB''
  have hAp : ∀ x : E, CS.phi u (A x) = CS.phi u x := fun x => by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hA x
  have hBp : ∀ x : E, CS.phi u (B x) = CS.phi u x := fun x => by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hB' x
  unfold monodromy
  ext x
  simp [hAp, hBp]

/-- A nonzero left eigenvector with eigenvalue 1 gives an exact unit
multiplier:  `∃ w ≠ 0, M w = w`  (so `1 ∈ σ(M)`, eq. (6.20)). -/
theorem eigenvalue_one_of_left_eigenvector {E : Type*} [AddCommGroup E] [Module ℝ E]
    [Module.Finite ℝ E] {M : E →ₗ[ℝ] E} {φ : E →ₗ[ℝ] ℝ}
    (h : φ ∘ₗ M = φ) (hφ : φ ≠ 0) : ∃ w : E, w ≠ 0 ∧ M w = w := by
  let g : E →ₗ[ℝ] E := M - 1
  -- φ ∘ g = 0
  have hcomp : φ ∘ₗ g = 0 := by
    ext x
    have hx : φ (M x) = φ x := by simpa [LinearMap.comp_apply] using LinearMap.congr_fun h x
    simp [g, hx]
  -- range g ≤ ker φ
  have hrange_le : LinearMap.range g ≤ LinearMap.ker φ := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact LinearMap.mem_ker.mpr (by simpa using LinearMap.congr_fun hcomp y)
  -- ker φ ≠ ⊤
  have hkerφ_ne_top : LinearMap.ker φ ≠ ⊤ := by
    intro htop
    apply hφ
    ext x
    have : x ∈ (⊤ : Submodule ℝ E) := trivial
    have : x ∈ LinearMap.ker φ := htop ▸ this
    exact LinearMap.mem_ker.mp this
  -- range g ≠ ⊤
  have hrange_ne_top : LinearMap.range g ≠ ⊤ := by
    intro hr
    apply hkerφ_ne_top
    apply le_antisymm
    · exact le_top
    · intro x _
      have : x ∈ LinearMap.range g := by simpa [hr]
      exact hrange_le this
  -- finrank range g < finrank E
  have hfinrank_range : Module.finrank ℝ (LinearMap.range g) < Module.finrank ℝ E := by
    exact Submodule.finrank_lt (by simpa using hrange_ne_top)
  -- rank–nullity: finrank range g + finrank ker g = finrank E
  have hrn : Module.finrank ℝ (LinearMap.range g) + Module.finrank ℝ (LinearMap.ker g) =
      Module.finrank ℝ E := LinearMap.finrank_range_add_finrank_ker g
  -- hence ker g ≠ ⊥
  have hker_ne_bot : LinearMap.ker g ≠ ⊥ := by
    intro hbot
    have hk : Module.finrank ℝ (LinearMap.ker g) = 0 := by
      rw [hbot]
      simp
    nlinarith [hrn, hfinrank_range, hk]
  rcases (Submodule.ne_bot_iff (LinearMap.ker g)).mp hker_ne_bot with ⟨w, hwmem, hwne⟩
  refine ⟨w, hwne, ?_⟩
  have hw : g w = 0 := LinearMap.mem_ker.mp hwmem
  unfold g at hw
  exact sub_eq_zero.mp hw

/-- Concretely: a fully clipped two-cycle whose one-step Jacobians admit the
neutral covector at `±u` has an exact unit multiplier.  Combines
Prop. 6.1 (opposite directions), Prop. 6.5 (pointwise neutrality) and the
rank argument above. -/
theorem fully_clipped_unit_multiplier {E : Type*} [AddCommGroup E] [Module ℝ E]
    [Module.Finite ℝ E] (CS : ClippingStructure E) {η c : ℝ} {A B : E →ₗ[ℝ] E} {u : E}
    (hu : CS.rho u = 1) (hφ : CS.phi u ≠ 0)
    (hA : CS.phi u ∘ₗ A = CS.phi u)
    (hB : CS.phi (-u) ∘ₗ B = CS.phi (-u)) :
    ∃ w : E, w ≠ 0 ∧ monodromy A B w = w := by
  exact eigenvalue_one_of_left_eigenvector
    (universal_unit_multiplier_left CS hu hA hB) hφ
