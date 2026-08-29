import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Lean4Proofs.Spectrum

/-!
# The completely solvable planar gradient model  (Paper_04, §7)

All statements here are exact polynomial/field algebra, machine-checked:

  * eq. (7.5)–(7.6)  `lam - bs + ds² > 0` for `s ≥ 0` given `b² < 4dlam`,
    and the sign law `x·g(x) > 0` for `x ≠ 0`;
  * eq. (7.7)  the smooth period-two equation `lam - 2/η = ba² - da⁴`;
  * eq. (7.9)–(7.10)  the quadratic for `q = a²` and its explicit root;
  * eq. (7.20)–(7.21)  the first-contact equation `Ψ(η,c) = 0` and
    `g(ηc/2) - c = (ηc/2)Ψ(η,c)`;
  * Thm. (planar separation coefficients)  if the polynomial ansatz
    `η(c) = 2/lam + K₂c² + K₄c⁴` satisfies `Ψ(η(c),c) = 0` on an interval
    `(0,ε)`, then `K₂ = 2b/lam⁴` and `K₄ = 6b²/lam⁷ - 2d/lam⁶`
    (eq. (7.23)–(7.24); the `O(c⁶)` remainder version is its asymptotic
    corollary);
  * Prop. 7.2  the exact step law `2a_c = ηc` of the fully clipped
    symmetric branch.
-/

namespace PlanarModel

/-- `g(x) = lamx - bx³ + dx⁵` (eq. (7.4)). -/
noncomputable def g (lam b d : ℝ) (x : ℝ) : ℝ := lam * x - b * x ^ 3 + d * x ^ 5

/-- `g(x) = x(lam - bx² + dx⁴)`. -/
lemma g_factor (lam b d x : ℝ) : g lam b d x = x * (lam - b * x ^ 2 + d * x ^ 4) := by
  unfold g; ring

/-- `lam - bs + ds² > 0` for `s ≥ 0` whenever `b² < 4dlam` and `lam, d > 0`
(eq. (7.5)).  Proof: if the quadratic were ≤ 0 at `s`, the discriminant
would have to be nonnegative. -/
lemma quadratic_positive {lam b d s : ℝ} (hlam : 0 < lam) (hd : 0 < d) (hdisc : b ^ 2 < 4 * d * lam)
    (hs : 0 ≤ s) : 0 < lam - b * s + d * s ^ 2 := by
  by_contra hc
  have hle : lam - b * s + d * s ^ 2 ≤ 0 := by
    push_neg at hc
    exact hc
  have hsq : (b - 2 * d * s) ^ 2 ≤ b ^ 2 - 4 * d * lam := by
    nlinarith [hle, hdisc, hd]
  have : (b - 2 * d * s) ^ 2 < 0 := by nlinarith [hsq, hdisc]
  exact not_lt_of_ge (sq_nonneg (b - 2 * d * s)) this

/-- `x·g(x) > 0` for `x ≠ 0` (eq. (7.6)). -/
lemma g_sign {lam b d : ℝ} (hlam : 0 < lam) (hd : 0 < d) (hdisc : b ^ 2 < 4 * d * lam)
    {x : ℝ} (hx : x ≠ 0) : 0 < x * g lam b d x := by
  rw [g_factor]
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hq := quadratic_positive hlam hd hdisc (sq_nonneg x)
  nlinarith [mul_pos hx2 hq]

/-- The smooth cycle equation: `f_η(a) = -a` ⟺ `lam - 2/η = ba² - da⁴`
(eq. (7.7)), for `η ≠ 0`, `a ≠ 0`. -/
lemma smooth_cycle_equation {lam b d η a : ℝ} (hη : η ≠ 0) (ha : a ≠ 0) :
    (1 - η * lam) * a + η * b * a ^ 3 - η * d * a ^ 5 = -a ↔
      lam - 2 / η = b * a ^ 2 - d * a ^ 4 := by
  constructor
  · intro h
    have h1 : (2 - η * lam + η * b * a ^ 2 - η * d * a ^ 4) * a = 0 := by
      nlinarith [h]
    have h2 : 2 - η * lam + η * b * a ^ 2 - η * d * a ^ 4 = 0 :=
      (mul_eq_zero.mp h1).resolve_right ha
    have h3 : 2 / η - lam + b * a ^ 2 - d * a ^ 4 = 0 := by
      have := congrArg (fun t : ℝ => t / η) h2
      field_simp [hη] at this ⊢
      linarith
    nlinarith [h3]
  · intro h
    have h3 : 2 / η - lam + b * a ^ 2 - d * a ^ 4 = 0 := by nlinarith [h]
    have h2 : 2 - η * lam + η * b * a ^ 2 - η * d * a ^ 4 = 0 := by
      have := congrArg (fun t : ℝ => t * η) h3
      field_simp [hη] at this ⊢
      linarith
    have h2a : (2 - η * lam + η * b * a ^ 2 - η * d * a ^ 4) * a = 0 := by
      simpa using congrArg (fun t : ℝ => t * a) h2
    have h2a' : 2 * a - η * lam * a + η * b * a ^ 3 - η * d * a ^ 5 = 0 := by nlinarith [h2a]
    nlinarith [h2a']

/-- `q = a²` satisfies the quadratic `dq² - bq + (lam - 2/η) = 0`
(eq. (7.9)). -/
lemma q_quadratic {lam b d η a q : ℝ} (hq : q = a ^ 2)
    (hcyc : lam - 2 / η = b * a ^ 2 - d * a ^ 4) :
    d * q ^ 2 - b * q + (lam - 2 / η) = 0 := by
  subst q
  nlinarith [hcyc]

/-- The explicit root `q = (b - √(b² - 4d(lam - 2/η)))/(2d)` solves the
quadratic (eq. (7.10)), for `d ≠ 0` and nonnegative discriminant. -/
lemma q_root {lam b d η : ℝ} (hd : d ≠ 0)
    (hdisc : 0 ≤ b ^ 2 - 4 * d * (lam - 2 / η))
    (q : ℝ) (hq : q = (b - Real.sqrt (b ^ 2 - 4 * d * (lam - 2 / η))) / (2 * d)) :
    d * q ^ 2 - b * q + (lam - 2 / η) = 0 := by
  subst q
  rw [div_pow]
  rw [show (b - Real.sqrt (b ^ 2 - 4 * d * (lam - 2 / η))) ^ 2 =
      b ^ 2 - 2 * b * Real.sqrt (b ^ 2 - 4 * d * (lam - 2 / η))
        + (Real.sqrt (b ^ 2 - 4 * d * (lam - 2 / η))) ^ 2 by ring]
  rw [Real.sq_sqrt hdisc]
  field_simp [hd]
  ring

/-- The first-contact equation (eq. (7.20)): `Ψ(η,c) := lam - 2/η - (b/4)η²c² + (d/16)η⁴c⁴`. -/
noncomputable def Psi (lam b d η c : ℝ) : ℝ := lam - 2 / η - b / 4 * η ^ 2 * c ^ 2 + d / 16 * η ^ 4 * c ^ 4

/-- Substituting the contact amplitude `a = ηc/2` into the cycle equation
`lam - 2/η = ba² - da⁴` gives exactly `Ψ(η,c) = 0` (eq. (7.20)). -/
lemma contact_equation {lam b d η c : ℝ} (hη : η ≠ 0) :
    (lam - 2 / η = b * (η * c / 2) ^ 2 - d * (η * c / 2) ^ 4) ↔ Psi lam b d η c = 0 := by
  unfold Psi
  constructor
  · intro h
    field_simp [hη] at h ⊢
    nlinarith
  · intro h
    field_simp [hη] at h ⊢
    nlinarith

/-- `g(ηc/2) - c = (ηc/2)·Ψ(η,c)` (eq. (7.21)). -/
lemma g_minus_c_Psi {lam b d η c : ℝ} (hη : η ≠ 0) :
    g lam b d (η * c / 2) - c = (η * c / 2) * Psi lam b d η c := by
  unfold g Psi
  field_simp [hη]
  ring

/-- At the switching contact the clipped pair lies on the switching boundary:
`g(ηc/2) = c` when `Ψ(η,c) = 0`. -/
lemma g_eq_c_of_Psi {lam b d η c : ℝ} (hη : η ≠ 0) (hΨ : Psi lam b d η c = 0) :
    g lam b d (η * c / 2) = c := by
  have hsub : g lam b d (η * c / 2) - c = 0 := by
    rw [g_minus_c_Psi hη, hΨ, mul_zero]
  exact sub_eq_zero.mp hsub

/-! ## Polynomial coefficient extraction for the separation law -/

open Polynomial

/-- The polynomial ansatz `η(c) = 2/lam + K₂c² + K₄c⁴`. -/
noncomputable def etaPoly (lam K₂ K₄ : ℝ) : Polynomial ℝ :=
  C (2 / lam) + C K₂ * X ^ 2 + C K₄ * X ^ 4

/-- `Q(c) := η(c)·Ψ(η(c),c)` as a polynomial in `c`:

    Q = lamη - 2 - (b/4)η³X² + (d/16)η⁵X⁴   (no division by `η`). -/
noncomputable def Qpoly (lam b d K₂ K₄ : ℝ) : Polynomial ℝ :=
  C lam * etaPoly lam K₂ K₄ - C 2 - C (b / 4) * (etaPoly lam K₂ K₄) ^ 3 * X ^ 2 +
    C (d / 16) * (etaPoly lam K₂ K₄) ^ 5 * X ^ 4

/-- Evaluating `Q` at `c` gives the real expression (no division). -/
lemma Qpoly_eval_no_division (lam b d K₂ K₄ c : ℝ) :
    (Qpoly lam b d K₂ K₄).eval c =
      lam * (2 / lam + K₂ * c ^ 2 + K₄ * c ^ 4) - 2
        - b / 4 * (2 / lam + K₂ * c ^ 2 + K₄ * c ^ 4) ^ 3 * c ^ 2
        + d / 16 * (2 / lam + K₂ * c ^ 2 + K₄ * c ^ 4) ^ 5 * c ^ 4 := by
  unfold Qpoly etaPoly
  simp [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]

/-- If `Ψ(η(c),c) = 0` then `Q(c) = 0`.  (The step size `η(c)` is forced
nonzero by `hΨ` unless `lam = 0`.) -/
lemma Qpoly_eq_zero_of_Psi {lam b d K₂ K₄ c : ℝ} (hlam : lam ≠ 0)
    (hΨ : Psi lam b d (2 / lam + K₂ * c ^ 2 + K₄ * c ^ 4) c = 0) :
    (Qpoly lam b d K₂ K₄).eval c = 0 := by
  let η : ℝ := 2 / lam + K₂ * c ^ 2 + K₄ * c ^ 4
  have hη : η ≠ 0 := by
    intro hz
    have : Psi lam b d η c = lam := by
      unfold Psi
      rw [hz]
      simp
    exact hlam (by rw [hΨ] at this; exact this.symm)
  have hq := Qpoly_eval_no_division lam b d K₂ K₄ c
  have hψ : lam * η - 2 - b / 4 * η ^ 3 * c ^ 2 + d / 16 * η ^ 5 * c ^ 4 =
      η * Psi lam b d η c := by
    unfold Psi
    field_simp [hη]
  rw [hq, hψ, hΨ, mul_zero]

/-- Coefficients of the ansatz polynomial `E`. -/
lemma E_coeff0 (lam K₂ K₄ : ℝ) : (etaPoly lam K₂ K₄).coeff 0 = 2 / lam := by
  unfold etaPoly
  simp [coeff_add, coeff_C, coeff_X_pow]

lemma E_coeff2 (lam K₂ K₄ : ℝ) : (etaPoly lam K₂ K₄).coeff 2 = K₂ := by
  unfold etaPoly
  simp [coeff_add, coeff_C, coeff_X_pow]

lemma E_coeff4 (lam K₂ K₄ : ℝ) : (etaPoly lam K₂ K₄).coeff 4 = K₄ := by
  unfold etaPoly
  simp [coeff_add, coeff_C, coeff_X_pow]

lemma E_coeff1 (lam K₂ K₄ : ℝ) : (etaPoly lam K₂ K₄).coeff 1 = 0 := by
  unfold etaPoly
  simp [coeff_add, coeff_C, coeff_X_pow]

/-- `(p³).coeff 0 = (p.coeff 0)³`. -/
lemma pow3_coeff0 (p : Polynomial ℝ) : (p ^ 3).coeff 0 = p.coeff 0 ^ 3 := by
  rw [show p ^ 3 = p * p ^ 2 by ring]
  rw [coeff_mul]
  simp
  rw [show p ^ 2 = p * p by ring]
  rw [coeff_mul]
  simp
  ring

/-- `(p⁵).coeff 0 = (p.coeff 0)⁵`. -/
lemma pow5_coeff0 (p : Polynomial ℝ) : (p ^ 5).coeff 0 = p.coeff 0 ^ 5 := by
  rw [show p ^ 5 = p * p ^ 4 by ring]
  rw [coeff_mul]
  simp
  rw [show p ^ 4 = p * p ^ 3 by ring]
  rw [coeff_mul]
  simp
  rw [show p ^ 3 = p * p ^ 2 by ring]
  rw [coeff_mul]
  simp
  rw [show p ^ 2 = p * p by ring]
  rw [coeff_mul]
  simp
  ring

/-- `(p³).coeff 2 = 3 p₀² p₂` when `p₁ = 0`. -/
lemma pow3_coeff2 (p : Polynomial ℝ) (hp1 : p.coeff 1 = 0) :
    (p ^ 3).coeff 2 = 3 * p.coeff 0 ^ 2 * p.coeff 2 := by
  rw [show p ^ 3 = p * p ^ 2 by ring]
  rw [coeff_mul]
  norm_num [Finset.antidiagonal]
  rw [show p ^ 2 = p * p by ring]
  rw [coeff_mul]
  norm_num [Finset.antidiagonal]
  rw [hp1]
  ring

/-- The coefficient of `c²` in `Q` (power matching, eq. (7.23) step 1). -/
lemma Qpoly_coeff_two (lam b d K₂ K₄ : ℝ) :
    (Qpoly lam b d K₂ K₄).coeff 2 = lam * K₂ - 2 * b / lam ^ 3 := by
  unfold Qpoly
  simp only [coeff_add, coeff_sub]
  rw [coeff_mul_X_pow]
  rw [coeff_C_mul, coeff_C_mul]
  rw [coeff_mul_X_pow']
  simp [coeff_C, coeff_X_pow]
  rw [pow3_coeff0, E_coeff0, E_coeff2]
  ring

/-- The coefficient of `c⁴` in `Q` (power matching, eq. (7.24) step 1). -/
lemma Qpoly_coeff_four (lam b d K₂ K₄ : ℝ) :
    (Qpoly lam b d K₂ K₄).coeff 4 = lam * K₄ - 3 * b * K₂ / lam ^ 2 + 2 * d / lam ^ 5 := by
  unfold Qpoly
  simp only [coeff_add, coeff_sub]
  rw [coeff_mul_X_pow, coeff_mul_X_pow]
  rw [coeff_C_mul, coeff_C_mul, coeff_C_mul]
  simp [coeff_C, coeff_X_pow]
  rw [pow3_coeff2 _ (E_coeff1 lam K₂ K₄), pow5_coeff0, E_coeff0, E_coeff2, E_coeff4]
  ring

/-- A polynomial that vanishes on an interval is zero. -/
lemma eq_zero_of_eval_zero_on_Ioo {ε : ℝ} (hε : 0 < ε) {p : Polynomial ℝ}
    (h : ∀ c : ℝ, c ∈ Set.Ioo 0 ε → p.eval c = 0) : p = 0 := by
  apply eq_zero_of_infinite_isRoot
  apply Set.Infinite.mono _ (Set.Ioo_infinite hε)
  intro c hc
  exact h c hc

/-- Theorem (planar separation coefficients, eq. (7.23)–(7.24)): if the
polynomial ansatz `η(c) = 2/lam + K₂c² + K₄c⁴` satisfies `Ψ(η(c),c) = 0`
for all `0 < c < ε`, then

    K₂ = 2b/lam⁴      and      K₄ = 6b²/lam⁷ - 2d/lam⁶.

These are exactly the coefficients the paper obtains by "comparing powers of
`c`"; the asymptotic statement `η_sc(c) = 2/lam + K₂c² + K₄c⁴ + O(c⁶)`
(eq. (7.22)) is the corresponding version with a remainder. -/
theorem planar_separation_coefficients {lam b d K₂ K₄ ε : ℝ} (hε : 0 < ε) (hlam : lam ≠ 0)
    (hΨ : ∀ c : ℝ, 0 < c → c < ε → Psi lam b d (2 / lam + K₂ * c ^ 2 + K₄ * c ^ 4) c = 0) :
    K₂ = 2 * b / lam ^ 4 ∧ K₄ = 6 * b ^ 2 / lam ^ 7 - 2 * d / lam ^ 6 := by
  -- Q ≡ 0 on (0, ε), hence Q = 0 as a polynomial, hence its coefficients vanish
  have hQzero : ∀ c : ℝ, c ∈ Set.Ioo 0 ε → (Qpoly lam b d K₂ K₄).eval c = 0 := by
    intro c hc
    exact Qpoly_eq_zero_of_Psi hlam (hΨ c hc.1 hc.2)
  have hQ : Qpoly lam b d K₂ K₄ = 0 := eq_zero_of_eval_zero_on_Ioo hε hQzero
  have hc2 : (Qpoly lam b d K₂ K₄).coeff 2 = 0 := by simp [hQ]
  have hc4 : (Qpoly lam b d K₂ K₄).coeff 4 = 0 := by simp [hQ]
  have hA : lam * K₂ - 2 * b / lam ^ 3 = 0 := by
    rw [Qpoly_coeff_two] at hc2
    exact hc2
  constructor
  · -- K₂ = 2b/lam⁴
    have : lam * K₂ = 2 * b / lam ^ 3 := by linarith
    field_simp [hlam] at this ⊢
    linarith
  · -- K₄ = 6b²/lam⁷ - 2d/lam⁶
    have hK₂ : K₂ = 2 * b / lam ^ 4 := by
      have : lam * K₂ = 2 * b / lam ^ 3 := by linarith
      field_simp [hlam] at this ⊢
      linarith
    have hB : lam * K₄ - 3 * b * K₂ / lam ^ 2 + 2 * d / lam ^ 5 = 0 := by
      rw [Qpoly_coeff_four] at hc4
      exact hc4
    rw [hK₂] at hB
    field_simp [hlam] at hB ⊢
    nlinarith

/-- Proposition 7.2: the exact step-length law of the symmetric clipped cycle
(eq. (7.34)): `2a_c = ηc` with `a_c = ηc/2`. -/
lemma exact_amplitude_saturation (η c : ℝ) : η * c / 2 - (-(η * c / 2)) = η * c := by
  ring

/-- For the model parameters of §7.7 (`lam = 2, ν = 1/2, b = 1, d = 1`):
`η_f = 1`, `ℓ₊ = 1`, `Γ₊ = 6`, `K₂ = 2b/lam⁴ = 1/8`. -/
lemma concrete_parameters :
    etaF 2 = 1 ∧ flipCoeff 6 2 = 1 ∧ 2 * 1 / 2 ^ 4 = 1 / 8 := by
  constructor
  · unfold etaF; norm_num
  · constructor
    · unfold flipCoeff; norm_num
    · norm_num

end PlanarModel