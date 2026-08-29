import Mathlib.Analysis.Normed.Module.Basic
import Lean4Proofs.Clipping
import Lean4Proofs.GradientBalance

/-!
# Switching geometry, continued  (Paper_04, §4–§6)
-/

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The period-two relations of the clipped map give equal clipped-output norms
(eq. (4.16)). -/
lemma clipped_output_equal_norms {η : ℝ} (hη : η ≠ 0) {c : ℝ} {gradV : E → E} {xm xp : E}
    (hcyc : ClippedTwoCycle η c gradV xm xp) :
    ‖clip c (gradV xp)‖ = ‖clip c (gradV xm)‖ := by
  have h1 : η • clip c (gradV xp) = xp - xm := by
    have hL : clippedMap η c gradV xp = xm := hcyc.left
    unfold clippedMap at hL
    rw [← hL]
    abel
  have h2 : η • clip c (gradV xm) = xm - xp := by
    have hR : clippedMap η c gradV xm = xp := hcyc.right
    unfold clippedMap at hR
    rw [← hR]
    abel
  have hn1 : ‖η • clip c (gradV xp)‖ = ‖xp - xm‖ := by rw [h1]
  have hn2 : ‖η • clip c (gradV xm)‖ = ‖xp - xm‖ := by
    rw [h2]
    rw [show ‖xm - xp‖ = ‖xp - xm‖ by rw [← neg_sub, norm_neg]]
  have hn1' : ‖η‖ * ‖clip c (gradV xp)‖ = ‖xp - xm‖ := by
    simpa [norm_smul] using hn1
  have hn2' : ‖η‖ * ‖clip c (gradV xm)‖ = ‖xp - xm‖ := by
    simpa [norm_smul] using hn2
  have hηabs : ‖η‖ ≠ 0 := norm_ne_zero_iff.mpr hη
  have : ‖η‖ * ‖clip c (gradV xp)‖ = ‖η‖ * ‖clip c (gradV xm)‖ := by
    rw [hn1', hn2']
  exact mul_left_cancel₀ hηabs this

/-- Proposition 4.8: no mixed smooth–clipped period-two itinerary (eq. (4.13)). -/
theorem no_mixed_period_two {η c : ℝ} (hη : η ≠ 0) (hc : 0 ≤ c) {gradV : E → E} {xm xp : E}
    (hcyc : ClippedTwoCycle η c gradV xm xp) :
    ¬ (‖gradV xm‖ < c ∧ c < ‖gradV xp‖) ∧ ¬ (‖gradV xp‖ < c ∧ c < ‖gradV xm‖) := by
  have heq : ‖clip c (gradV xp)‖ = ‖clip c (gradV xm)‖ := clipped_output_equal_norms hη hcyc
  have hnormP : ‖clip c (gradV xp)‖ = min ‖gradV xp‖ c := norm_clip hc _
  have hnormM : ‖clip c (gradV xm)‖ = min ‖gradV xm‖ c := norm_clip hc _
  constructor
  · rintro ⟨hm, hp⟩
    have h1 : min ‖gradV xm‖ c = ‖gradV xm‖ := min_eq_left (le_of_lt hm)
    have h2 : min ‖gradV xp‖ c = c := min_eq_right (le_of_lt hp)
    have : ‖gradV xm‖ = c := by
      calc
        ‖gradV xm‖ = min ‖gradV xm‖ c := h1.symm
        _ = ‖clip c (gradV xm)‖ := hnormM.symm
        _ = ‖clip c (gradV xp)‖ := heq.symm
        _ = min ‖gradV xp‖ c := hnormP
        _ = c := h2
    exact (ne_of_lt hm) this
  · rintro ⟨hp, hm⟩
    have h1 : min ‖gradV xp‖ c = ‖gradV xp‖ := min_eq_left (le_of_lt hp)
    have h2 : min ‖gradV xm‖ c = c := min_eq_right (le_of_lt hm)
    have : ‖gradV xp‖ = c := by
      calc
        ‖gradV xp‖ = min ‖gradV xp‖ c := h1.symm
        _ = ‖clip c (gradV xp)‖ := hnormP.symm
        _ = ‖clip c (gradV xm)‖ := heq
        _ = min ‖gradV xm‖ c := hnormM
        _ = c := h2
    exact (ne_of_lt hp) this

/-- Proposition 6.1: exact geometry of a fully clipped two-cycle (eq. (6.2)–(6.5)). -/
theorem fully_clipped_geometry {η c : ℝ} (hη : 0 < η) (hc : 0 < c) {gradV : E → E} {xm xp : E}
    (hcyc : ClippedTwoCycle η c gradV xm xp) (hp : c < ‖gradV xp‖) (hm : c < ‖gradV xm‖) :
    ‖xp - xm‖ = η * c ∧
      ∃ u : E, ‖u‖ = 1 ∧ gradV xp = ‖gradV xp‖ • u ∧ gradV xm = -‖gradV xm‖ • u := by
  have h1 : η • clip c (gradV xp) = xp - xm := by
    have hL : clippedMap η c gradV xp = xm := hcyc.left
    unfold clippedMap at hL
    rw [← hL]
    abel
  have h2 : η • clip c (gradV xm) = xm - xp := by
    have hR : clippedMap η c gradV xm = xp := hcyc.right
    unfold clippedMap at hR
    rw [← hR]
    abel
  have hnormP : ‖clip c (gradV xp)‖ = c := by
    rw [norm_clip (le_of_lt hc)]
    exact min_eq_right (le_of_lt hp)
  constructor
  · have hn1 : ‖η • clip c (gradV xp)‖ = ‖xp - xm‖ := by rw [h1]
    rw [norm_smul] at hn1
    rw [hnormP, Real.norm_eq_abs, abs_of_pos hη] at hn1
    exact hn1.symm
  · let u : E := (1 / (η * c)) • (xp - xm)
    refine ⟨u, ?_, ?_, ?_⟩
    · have hn1 : ‖η • clip c (gradV xp)‖ = ‖xp - xm‖ := by rw [h1]
      rw [norm_smul, hnormP, Real.norm_eq_abs, abs_of_pos hη] at hn1
      have hlen : ‖xp - xm‖ = η * c := hn1.symm
      unfold u
      rw [norm_smul]
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (mul_pos hη hc))]
      rw [hlen]
      field_simp [ne_of_gt hη, ne_of_gt hc]
    · have hcl : clip c (gradV xp) = (c / ‖gradV xp‖) • gradV xp := clip_of_lt (le_of_lt hc) hp
      have hh1 : η • ((c / ‖gradV xp‖) • gradV xp) = xp - xm := by
        rw [← hcl]; exact h1
      have hh1' : (η * c / ‖gradV xp‖) • gradV xp = xp - xm := by
        simpa [smul_smul, div_eq_mul_inv, mul_assoc] using hh1
      have hh2 : (‖gradV xp‖ / (η * c)) • ((η * c / ‖gradV xp‖) • gradV xp) =
          (‖gradV xp‖ / (η * c)) • (xp - xm) := by rw [hh1']
      rw [smul_smul] at hh2
      have hscalar : (‖gradV xp‖ / (η * c)) * (η * c / ‖gradV xp‖) = 1 := by
        field_simp [ne_of_gt (lt_trans hc hp), ne_of_gt hη, ne_of_gt hc]
      rw [hscalar, one_smul] at hh2
      unfold u
      rw [smul_smul]
      have hq : ‖gradV xp‖ * (1 / (η * c)) = ‖gradV xp‖ / (η * c) := by ring
      rw [hq]
      exact hh2
    · have hcl : clip c (gradV xm) = (c / ‖gradV xm‖) • gradV xm := clip_of_lt (le_of_lt hc) hm
      have hh1 : η • ((c / ‖gradV xm‖) • gradV xm) = xm - xp := by
        rw [← hcl]; exact h2
      have hh1' : (η * c / ‖gradV xm‖) • gradV xm = -(xp - xm) := by
        rw [← neg_sub] at hh1
        simpa [smul_smul, div_eq_mul_inv, mul_assoc] using hh1
      have hh2 : (‖gradV xm‖ / (η * c)) • ((η * c / ‖gradV xm‖) • gradV xm) =
          (‖gradV xm‖ / (η * c)) • (-(xp - xm)) := by rw [hh1']
      rw [smul_smul] at hh2
      have hscalar : (‖gradV xm‖ / (η * c)) * (η * c / ‖gradV xm‖) = 1 := by
        field_simp [ne_of_gt (lt_trans hc hm), ne_of_gt hη, ne_of_gt hc]
      rw [hscalar, one_smul] at hh2
      rw [smul_neg] at hh2
      unfold u
      rw [neg_smul, smul_smul]
      have hq : ‖gradV xm‖ * (1 / (η * c)) = ‖gradV xm‖ / (η * c) := by ring
      rw [hq]
      exact hh2
