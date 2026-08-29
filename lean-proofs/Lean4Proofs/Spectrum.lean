import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Spectral consequences and the flip threshold  (Paper_04, §1.6, §3)

Machine-checked versions of:

  * `ρ_i(η) = 1 - η lam_i`  (eq. (1.13));
  * `ρ_d(η_f) = -1`, `η_f = 2/lam₊`  (eq. (1.14), (1.15));
  * transversal crossing `dρ/dη|_ηf = -lam₊ ≠ 0`  (eq. (1.22));
  * non-critical spectrum `-1 < 1 - 2lam_i/lam₊ < 1`  (eq. (1.19));
  * `ρ_*(μ) = -1 - lam₊ μ`  (eq. (3.3)).
-/

/-- The multipliers of `DG_η(x_*)`: `ρ_i(η) = 1 - η lam_i` (eq. (1.13)). -/
noncomputable def multiplier (η lam : ℝ) : ℝ := 1 - η * lam

/-- The distinguished step size `η_f = 2/lam₊` (eq. (1.15)). -/
noncomputable def etaF (lamstar : ℝ) : ℝ := 2 / lamstar

/-- `ρ_d(η_f) = -1` (eq. (1.16)). -/
lemma multiplier_eta_f {lam : ℝ} (hlam : lam ≠ 0) : multiplier (etaF lam) lam = -1 := by
  unfold multiplier etaF
  field_simp [hlam]
  norm_num

/-- `d/dη ρ(η) = -lam` (eq. (1.21)). -/
lemma multiplier_deriv (lam : ℝ) : deriv (fun η : ℝ => multiplier η lam) = fun _ => -lam := by
  funext η
  unfold multiplier
  -- 1 - η * lam  =  (fun η => 1) - (fun η => lam * η)
  rw [show (fun η : ℝ => 1 - η * lam) = (fun η : ℝ => 1) - (fun η : ℝ => lam * η) by
    ext; simp; ring]
  rw [deriv_sub (by fun_prop) (by fun_prop)]
  simp [deriv_const, deriv_const_mul_id]

/-- The critical multiplier crosses `-1` transversally: `dρ/dη(η_f) ≠ 0`
(eq. (1.22)). -/
theorem transversal_crossing {lam : ℝ} (hlampos : 0 < lam) :
    multiplier (etaF lam) lam = -1 ∧ deriv (fun η : ℝ => multiplier η lam) (etaF lam) ≠ 0 := by
  constructor
  · exact multiplier_eta_f (ne_of_gt hlampos)
  · rw [multiplier_deriv]
    simp [hlampos.ne']

/-- Non-critical spectrum at `η = η_f`:  for `0 < lam_i < lam₊`,
`-1 < 1 - 2lam_i/lam₊ < 1`  (eq. (1.19)). -/
theorem noncritical_spectrum {lami lamstar : ℝ} (hlamstar : 0 < lamstar) (hlami : 0 < lami)
    (hlt : lami < lamstar) : -1 < 1 - 2 * lami / lamstar ∧ 1 - 2 * lami / lamstar < 1 := by
  have hdiv : 2 * lami / lamstar < 2 := by
    -- 2lami/lamstar < 2  ⟺  2lami < 2lamstar  (lamstar > 0)
    rw [div_lt_iff₀ hlamstar]
    nlinarith [hlt]
  constructor
  · nlinarith [hdiv]
  · have hpos : 0 < 2 * lami / lamstar := by positivity
    nlinarith [hpos]

/-- The critical multiplier in the bifurcation parameter `μ`:
`ρ_*(μ) = 1 - (η_f + μ)lam₊ = -1 - lam₊ μ`  (eq. (3.3)). -/
lemma critical_multiplier_mu {lamstar : ℝ} (hlam : lamstar ≠ 0) (μ : ℝ) :
    multiplier (etaF lamstar + μ) lamstar = -1 - lamstar * μ := by
  unfold multiplier etaF
  field_simp [hlam]
  ring

/-- The flip coefficient: `ℓ₊ = Γ₊/(3lam₊)` (eq. (1.23)). -/
noncomputable def flipCoeff (Γ lamstar : ℝ) : ℝ := Γ / (3 * lamstar)

/-- `ℓ₊ > 0` follows from `Γ₊ > 0` and `lam₊ > 0` (H4). -/
lemma flipCoeff_pos {Γ lamstar : ℝ} (hΓ : 0 < Γ) (hlam : 0 < lamstar) :
    0 < flipCoeff Γ lamstar := by
  unfold flipCoeff
  positivity