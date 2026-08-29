import Mathlib.Analysis.Normed.Module.Basic
import Lean4Proofs.Clipping

/-!
# Exact gradient balance and switching geometry  (Paper_04, §4–§5)

Formal statements (all machine-checked):

  * Prop. 4.1  exact gradient balance on a smooth period-two cycle;
  * Lemma 4.4  midpoint–difference equations;
  * Thm. 5.1   simultaneous switching contact of the two cycle points;
  * Prop. 4.8   no mixed smooth–clipped period-two itinerary;
  * Prop. 6.1   exact geometry of a fully clipped two-cycle.
-/

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A genuine period-two cycle of the smooth map `G_η` (eq. (4.1)). -/
structure SmoothTwoCycle (η : ℝ) (gradV : E → E) (xm xp : E) : Prop where
  left : gradDescend η gradV xp = xm
  right : gradDescend η gradV xm = xp
  distinct : xp ≠ xm

/-- A period-two cycle of the clipped map `F_{η,c}` (eq. (6.1)). -/
structure ClippedTwoCycle (η c : ℝ) (gradV : E → E) (xm xp : E) : Prop where
  left : clippedMap η c gradV xp = xm
  right : clippedMap η c gradV xm = xp

/-- From `xp - ηgradV(xp) = xm` we get `ηgradV(xp) = xp - xm`. -/
lemma gradDescend_sub {η : ℝ} {gradV : E → E} {xp xm : E}
    (h : gradDescend η gradV xp = xm) : η • gradV xp = xp - xm := by
  unfold gradDescend at h
  rw [← h]
  abel

/-- Proposition 4.1: exact gradient balance on a smooth two-cycle (eq. (4.3)). -/
theorem exact_gradient_balance {η : ℝ} (hη : η ≠ 0) {gradV : E → E} {xm xp : E}
    (hcyc : SmoothTwoCycle η gradV xm xp) :
    gradV xp = (1 / η) • (xp - xm) ∧ gradV xm = -(1 / η) • (xp - xm) := by
  have h1 : η • gradV xp = xp - xm := gradDescend_sub hcyc.left
  have h2 : η • gradV xm = xm - xp := gradDescend_sub hcyc.right
  constructor
  · have := congrArg (fun t : E => (1 / η) • t) h1
    rw [smul_smul] at this
    have hsc : (1 / η) * η = 1 := by field_simp [hη]
    rw [hsc, one_smul] at this
    exact this
  · have h2' : η • gradV xm = -(xp - xm) := by
      rw [← neg_sub] at h2
      exact h2
    have := congrArg (fun t : E => (1 / η) • t) h2'
    rw [smul_smul] at this
    have hsc : (1 / η) * η = 1 := by field_simp [hη]
    rw [hsc, one_smul] at this
    rw [smul_neg] at this
    rw [neg_smul]
    exact this

/-- Corollary: the two gradients are exactly opposite (eq. (4.4)). -/
theorem opposite_gradients {η : ℝ} (hη : η ≠ 0) {gradV : E → E} {xm xp : E}
    (hcyc : SmoothTwoCycle η gradV xm xp) : gradV xp = -gradV xm := by
  rcases exact_gradient_balance hη hcyc with ⟨h₁, h₂⟩
  rw [h₁, h₂]
  simp

/-- Corollary: equal gradient norms for every norm (eq. (4.5)). -/
theorem equal_gradient_norms {η : ℝ} (hη : η ≠ 0) {gradV : E → E} {xm xp : E}
    (hcyc : SmoothTwoCycle η gradV xm xp) : ‖gradV xp‖ = ‖gradV xm‖ := by
  rw [opposite_gradients hη hcyc]
  simp

/-- Lemma 4.4: midpoint–difference equations (eq. (4.11)–(4.12)). -/
theorem midpoint_difference_equations {η : ℝ} (hη : η ≠ 0) {gradV : E → E} {x0 m d : E}
    (hcyc : SmoothTwoCycle η gradV (x0 + m - d) (x0 + m + d)) :
    gradV (x0 + m + d) + gradV (x0 + m - d) = 0 ∧
      gradV (x0 + m + d) - gradV (x0 + m - d) = (4 / η) • d := by
  rcases exact_gradient_balance hη hcyc with ⟨h₁, h₂⟩
  have htwo : (2 : ℝ) • d = d + d := by
    calc
      (2 : ℝ) • d = (1 + 1 : ℝ) • d := by norm_num
      _ = (1 : ℝ) • d + (1 : ℝ) • d := by rw [add_smul]
      _ = d + d := by simp
  have hd : (x0 + m + d) - (x0 + m - d) = (2 : ℝ) • d := by
    calc
      (x0 + m + d) - (x0 + m - d) = d + d := by abel
      _ = (2 : ℝ) • d := htwo.symm
  constructor
  · rw [h₁, h₂, hd]
    rw [neg_smul]
    simp
  · rw [h₁, h₂, hd]
    rw [neg_smul, sub_neg_eq_add]
    rw [← smul_add, ← add_smul]
    rw [smul_smul]
    have hsc : (1 / η) * (2 + 2) = 4 / η := by ring
    rw [hsc]