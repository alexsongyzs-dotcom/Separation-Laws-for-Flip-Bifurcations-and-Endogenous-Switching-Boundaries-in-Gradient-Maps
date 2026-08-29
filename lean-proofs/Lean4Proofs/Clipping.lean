import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Basic

/-!
# The radial gradient-clipping operator  (Paper_04, §1)

Formalizes the clipping operator (eq. 1.1–1.6):

    C_c^⋄(g) = min {1, c / ‖g‖} g,     C_c^⋄(0) = 0

and the two branches of the clipped gradient map.  All statements below
are exact and machine-checked.
-/

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial clipping operator `C_c^⋄` of the paper (eq. (1.1)).
Note: when `‖g‖ = 0`, division by zero gives `c/0 = 0` and `min 1 0 = 0`,
so `clip c 0 = 0` as required by the paper's convention. -/
noncomputable def clip (c : ℝ) (g : E) : E := min 1 (c / ‖g‖) • g

/-- `‖C_c(g)‖ = min {‖g‖, c}` for `0 ≤ c`  (eq. (1.11)). -/
lemma norm_clip {c : ℝ} (hc : 0 ≤ c) (g : E) : ‖clip c g‖ = min ‖g‖ c := by
  unfold clip
  rw [norm_smul]
  have hmin : 0 ≤ min 1 (c / ‖g‖) := by
    exact le_min zero_le_one (div_nonneg hc (norm_nonneg g))
  rw [Real.norm_eq_abs, abs_of_nonneg hmin]
  rcases lt_or_ge c ‖g‖ with hgt | hle
  · -- c < ‖g‖ :  min 1 (c/‖g‖) = c/‖g‖,  ‖g‖·(c/‖g‖) = c = min ‖g‖ c
    have hgpos : 0 < ‖g‖ := lt_of_le_of_lt hc hgt
    have hdiv : c / ‖g‖ < 1 := (div_lt_one hgpos).2 hgt
    rw [min_eq_right (le_of_lt hdiv)]
    rw [div_mul_cancel₀ c (ne_of_gt hgpos)]
    exact (min_eq_right (le_of_lt hgt)).symm
  · -- ‖g‖ ≤ c :  min 1 (c/‖g‖) = 1,  ‖g‖ = min ‖g‖ c
    by_cases hz : ‖g‖ = 0
    · rw [hz]; simp [hc]
    · have hgpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hz)
      have hone : 1 ≤ c / ‖g‖ := (one_le_div hgpos).2 hle
      rw [min_eq_left (by simpa using hone)]
      simp [min_eq_left hle]

/-- If `‖g‖ ≤ c` then clipping is inactive: `C_c(g) = g`. -/
lemma clip_of_le {c : ℝ} (_hc : 0 ≤ c) {g : E} (h : ‖g‖ ≤ c) : clip c g = g := by
  unfold clip
  by_cases hz : ‖g‖ = 0
  · have hg0 : g = 0 := norm_eq_zero.mp hz
    rw [hg0]
    simp
  · have hgpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hz)
    have hone : 1 ≤ c / ‖g‖ := (one_le_div hgpos).2 h
    rw [min_eq_left (by simpa using hone)]
    simp

/-- If `c < ‖g‖` then clipping rescales radially (eq. (1.4)). -/
lemma clip_of_lt {c : ℝ} (hc : 0 ≤ c) {g : E} (h : c < ‖g‖) : clip c g = (c / ‖g‖) • g := by
  unfold clip
  have hgpos : 0 < ‖g‖ := lt_of_le_of_lt hc h
  have hdiv : c / ‖g‖ < 1 := (div_lt_one hgpos).2 h
  rw [min_eq_right (le_of_lt hdiv)]

/-- `C_c(g) = g ⟺ ‖g‖ ≤ c` (for `0 ≤ c`). -/
lemma clip_eq_self_iff {c : ℝ} (hc : 0 ≤ c) (g : E) : clip c g = g ↔ ‖g‖ ≤ c := by
  constructor
  · intro h
    have : ‖clip c g‖ = ‖g‖ := by rw [h]
    rw [norm_clip hc] at this
    exact (min_eq_left_iff.mp this)
  · exact clip_of_le hc

/-- Clipping is odd: `C_c(-g) = -C_c(g)`. -/
lemma clip_neg (c : ℝ) (g : E) : clip c (-g) = -clip c g := by
  simp [clip, norm_neg]

/-- The clipped output is zero only at zero (for `0 < c`). -/
lemma clip_eq_zero_iff {c : ℝ} (hc : 0 < c) (g : E) : clip c g = 0 ↔ g = 0 := by
  constructor
  · intro h
    have hnorm : ‖clip c g‖ = 0 := by simp [h]
    rw [norm_clip (le_of_lt hc)] at hnorm
    rcases lt_or_ge c ‖g‖ with hgt | hle
    · rw [min_eq_right (le_of_lt hgt)] at hnorm
      have : c = 0 := hnorm
      exact False.elim (ne_of_gt hc this)
    · rw [min_eq_left hle] at hnorm
      exact norm_eq_zero.mp hnorm
  · intro h
    simp [clip, h]

/-! ## The two branches of the clipped gradient map (eq. (1.6)–(1.8)) -/

/-- The smooth gradient-descent map `G_η(x) = x - η ∇V(x)` (eq. (1.2)). -/
noncomputable def gradDescend (η : ℝ) (gradV : E → E) (x : E) : E := x - η • gradV x

/-- The clipped gradient map `F_{η,c}(x) = x - η C_c(∇V(x))` (eq. (1.5)). -/
noncomputable def clippedMap (η c : ℝ) (gradV : E → E) (x : E) : E := x - η • clip c (gradV x)

/-- On the smooth region `Ω_c⁻ = {‖∇V x‖ < c}` the maps coincide (eq. (1.6)). -/
lemma clippedMap_eq_gradDescend_of_lt {η c : ℝ} (hc : 0 ≤ c) (gradV : E → E) {x : E}
    (h : ‖gradV x‖ < c) : clippedMap η c gradV x = gradDescend η gradV x := by
  simp [clippedMap, gradDescend, clip_of_le hc (le_of_lt h)]

/-- On the clipped region `Ω_c⁺ = {c < ‖∇V x‖}` the radial branch holds (eq. (1.7)). -/
lemma clippedMap_eq_of_lt {η c : ℝ} (hc : 0 ≤ c) (gradV : E → E) {x : E}
    (h : c < ‖gradV x‖) : clippedMap η c gradV x = x - η • ((c / ‖gradV x‖) • gradV x) := by
  simp [clippedMap, clip_of_lt hc h]

/-- The smooth branch holds on the boundary `{‖∇V x‖ = c}` as well. -/
lemma clippedMap_eq_gradDescend_of_eq {η c : ℝ} (hc : 0 ≤ c) (gradV : E → E) {x : E}
    (h : ‖gradV x‖ = c) : clippedMap η c gradV x = gradDescend η gradV x := by
  simp [clippedMap, gradDescend, clip_of_le hc (le_of_eq h)]
