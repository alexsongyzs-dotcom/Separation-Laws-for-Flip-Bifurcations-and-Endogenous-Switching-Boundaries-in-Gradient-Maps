import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Flip normal-form algebra  (Paper_04, §3)

The truncated flip normal form `f_μ(z) = -(1 + lamμ)z + ℓ z³` (eq. (3.5) with
`R ≡ 0`).  Machine-checked:

  * exact second iterate  (Lemma 3.1, the algebraic part of eq. (3.7));
  * `f(z) = -z` at the amplitude point `z² = lamμ/ℓ`;
  * exact two-step multiplier `(f²)'(z) = (1 - 2lamμ)²` there — which
    implies the paper's `ρ = 1 - 4lamμ + O(μ^{3/2})` (eq. (3.15));
  * the amplitude identity `A₊² = lam₊/ℓ₊ = 3lam₊²/Γ₊` (eq. (3.20));
  * the separation-coefficient algebra `K = 1/(lam²A²‖v‖²) = ℓ/(lam³‖v‖²) = Γ/(3lam⁴‖v‖²)`
    (eq. (5.15)–(5.17)).
-/

/-- The truncated flip normal form (eq. (3.5), `R ≡ 0`): `f_μ(z) = -(1+lamμ)z + ℓz³`. -/
noncomputable def flipNF (lam ℓ μ : ℝ) (z : ℝ) : ℝ := -(1 + lam * μ) * z + ℓ * z ^ 3

/-- The normal form is odd in `z` (used in the paper: the two points of the
cycle are symmetric about the origin in reduced coordinates). -/
lemma flipNF_odd (lam ℓ μ z : ℝ) : flipNF lam ℓ μ (-z) = -flipNF lam ℓ μ z := by
  unfold flipNF
  ring

/-- Exact second iterate of the truncated normal form (Lemma 3.1; the algebraic
core of eq. (3.7)). -/
lemma second_iterate_exact (lam ℓ μ z : ℝ) :
    flipNF lam ℓ μ (flipNF lam ℓ μ z) =
      (1 + lam * μ) ^ 2 * z - ℓ * (1 + lam * μ) * (1 + (1 + lam * μ) ^ 2) * z ^ 3
        + 3 * ℓ ^ 2 * (1 + lam * μ) ^ 2 * z ^ 5
        - 3 * ℓ ^ 3 * (1 + lam * μ) * z ^ 7
        + ℓ ^ 4 * z ^ 9 := by
  unfold flipNF
  ring

/-- `f²(z) - z` (the fixed-point equation for period-two points), exactly
(eq. (3.7)). -/
lemma second_iterate_minus_z (lam ℓ μ z : ℝ) :
    flipNF lam ℓ μ (flipNF lam ℓ μ z) - z =
      ((1 + lam * μ) ^ 2 - 1) * z - ℓ * (1 + lam * μ) * (1 + (1 + lam * μ) ^ 2) * z ^ 3
        + 3 * ℓ ^ 2 * (1 + lam * μ) ^ 2 * z ^ 5
        - 3 * ℓ ^ 3 * (1 + lam * μ) * z ^ 7
        + ℓ ^ 4 * z ^ 9 := by
  rw [second_iterate_exact]
  ring

/-- `(1+lamμ)² - 1 = 2lamμ + lam²μ²` (used in eq. (3.10)). -/
lemma a_sq_sub_one (lam μ : ℝ) : (1 + lam * μ) ^ 2 - 1 = 2 * lam * μ + lam ^ 2 * μ ^ 2 := by
  ring

/-- At the amplitude point `z² = lamμ/ℓ` the truncated normal form satisfies
`f_μ(z) = -z`: the two cycle points are exchanged by one step. -/
lemma flipNF_neg_at_amplitude {lam ℓ μ : ℝ} (hℓ : ℓ ≠ 0) {z : ℝ}
    (hz : z ^ 2 = lam * μ / ℓ) : flipNF lam ℓ μ z = -z := by
  unfold flipNF
  rw [show z ^ 3 = z * z ^ 2 by ring]
  rw [hz]
  field_simp [hℓ]
  ring

/-- Consequently `f²(z) = z` at the amplitude point (a period-two point of
the truncated map). -/
lemma second_iterate_fixed_at_amplitude {lam ℓ μ : ℝ} (hℓ : ℓ ≠ 0) {z : ℝ}
    (hz : z ^ 2 = lam * μ / ℓ) : flipNF lam ℓ μ (flipNF lam ℓ μ z) = z := by
  rw [flipNF_neg_at_amplitude hℓ hz, flipNF_odd, flipNF_neg_at_amplitude hℓ hz]
  simp

/-- The leading amplitude balance: `z(2lamμ - 2ℓz²) = 0` at `z² = lamμ/ℓ`
(eq. (3.8), `lam₊μ ~ ℓ₊z²`). -/
lemma amplitude_balance {lam ℓ μ : ℝ} (hℓ : ℓ ≠ 0) (z : ℝ) (hz : z ^ 2 = lam * μ / ℓ) :
    2 * lam * μ * z - 2 * ℓ * z ^ 3 = 0 := by
  have hz' : z ^ 3 = z * (lam * μ / ℓ) := by
    calc
      z ^ 3 = z * z ^ 2 := by ring
      _ = z * (lam * μ / ℓ) := by rw [hz]
  rw [hz']
  field_simp [hℓ]
  ring

/-- The implicit-function nondegeneracy: `∂_w F(w,0) = lam₊ - 3ℓ₊w² = -2lam₊ ≠ 0`
at `w = ±√(lam₊/ℓ₊)` (eq. (3.24)). -/
lemma ift_nondegenerate {lam ℓ : ℝ} (hℓ : ℓ ≠ 0) {w : ℝ} (hw : w ^ 2 = lam / ℓ) :
    lam - 3 * ℓ * w ^ 2 = -2 * lam := by
  rw [hw]
  field_simp [hℓ]
  ring

/-- Exact two-step multiplier at the amplitude point (the algebraic core of
eq. (3.15)):  `(f²)'(z) = (1 - 2lamμ)² = 1 - 4lamμ + 4lam²μ²`.
(For small `μ` this gives the paper's `1 - 4lamμ + O(μ^{3/2})`.) -/
lemma two_step_multiplier_at_amplitude {lam ℓ μ : ℝ} (hℓ : ℓ ≠ 0) {z : ℝ}
    (hz : z ^ 2 = lam * μ / ℓ) :
    (-(1 + lam * μ) + 3 * ℓ * (flipNF lam ℓ μ z) ^ 2) *
        (-(1 + lam * μ) + 3 * ℓ * z ^ 2) = (1 - 2 * lam * μ) ^ 2 := by
  rw [flipNF_neg_at_amplitude hℓ hz]
  rw [neg_sq]
  rw [hz]
  field_simp [hℓ]
  ring_nf

/-- The cycle is attracting for small `μ > 0`: `(1 - 2lamμ)² < 1` whenever
`0 < lamμ < 1` (so the multiplier lies strictly inside the unit disk). -/
lemma cycle_multiplier_lt_one {lam μ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ) (hμ' : lam * μ < 1) :
    (1 - 2 * lam * μ) ^ 2 < 1 := by
  rw [sq_lt_one_iff_abs_lt_one, abs_lt]
  constructor
  · nlinarith [hμ', hlam, hμ]
  · nlinarith [hlam, hμ]

/-! ## Coefficient algebra (amplitude and separation law) -/

/-- `A₊² = lam₊/ℓ₊`  (eq. (3.19)). -/
noncomputable def A2 (lamstar ℓstar : ℝ) : ℝ := lamstar / ℓstar

/-- `A₊² = 3lam₊²/Γ₊` given `ℓ₊ = Γ₊/(3lam₊)` (eq. (3.20)). -/
lemma amplitude_algebra {lam Γ : ℝ} (hlam : lam ≠ 0) {ℓ : ℝ} (hℓ : ℓ = Γ / (3 * lam)) :
    A2 lam ℓ = 3 * lam ^ 2 / Γ := by
  unfold A2
  rw [hℓ]
  field_simp [hlam]

/-- `K = 1/(lam₊²A₊²‖v₊‖²) = ℓ₊/(lam₊³‖v₊‖²)`  (eq. (5.16)). -/
lemma separation_coefficient_ell {lam ℓ A vnorm : ℝ} (hA : A ^ 2 = lam / ℓ)
    (hlam : lam ≠ 0) (hℓ : ℓ ≠ 0) (hv : vnorm ≠ 0) :
    1 / (lam ^ 2 * A ^ 2 * vnorm ^ 2) = ℓ / (lam ^ 3 * vnorm ^ 2) := by
  rw [hA]
  field_simp [hlam, hℓ, hv]

/-- `K = Γ₊/(3lam₊⁴‖v₊‖²)`  (eq. (5.17)). -/
lemma separation_coefficient_Gamma {lam Γ ℓ A vnorm : ℝ} (hA : A ^ 2 = lam / ℓ)
    (hℓ : ℓ = Γ / (3 * lam)) (hlam : lam ≠ 0) (hℓ' : ℓ ≠ 0) (hv : vnorm ≠ 0) :
    1 / (lam ^ 2 * A ^ 2 * vnorm ^ 2) = Γ / (3 * lam ^ 4 * vnorm ^ 2) := by
  rw [separation_coefficient_ell hA hlam hℓ' hv]
  rw [hℓ]
  field_simp [hlam, hv]

/-- `K > 0` from `Γ₊ > 0`, `lam₊ > 0`, `‖v₊‖ ≠ 0` (H4; eq. (5.18)). -/
lemma separation_coefficient_pos {lam Γ vnorm : ℝ} (hlam : 0 < lam) (hΓ : 0 < Γ)
    (hv : vnorm ≠ 0) : 0 < Γ / (3 * lam ^ 4 * vnorm ^ 2) := by
  have hv2 : 0 < vnorm ^ 2 := sq_pos_of_ne_zero hv
  positivity