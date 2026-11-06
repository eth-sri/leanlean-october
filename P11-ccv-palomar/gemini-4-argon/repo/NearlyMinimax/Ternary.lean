module

public import Mathlib

@[expose] public section

/-! # The three-point response law

This file formalizes the finite response law in Section 6.1 of the paper.
Index 0 represents `-a`, index 1 represents `0`, and index 2 represents `a`.
Expectations are actual finite sums against the specified masses.
-/

namespace NearlyMinimax

open scoped Topology

noncomputable section

/-- The support of the paper's three-point response law. -/
def ternaryValue (a : ℝ) : Fin 3 → ℝ := ![-a, 0, a]

/-- The three probability masses; positivity is proved separately. -/
def ternaryMass (a f V : ℝ) : Fin 3 → ℝ :=
  ![(V + f ^ 2 - a * f) / (2 * a ^ 2),
    1 - (V + f ^ 2) / a ^ 2,
    (V + f ^ 2 + a * f) / (2 * a ^ 2)]

/-- Integration against the finite response law. -/
def ternaryExpectation (a f V : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑ y : Fin 3, ternaryMass a f V y * g (ternaryValue a y)

theorem ternary_normalized (a f V ) (ha : a ≠ 0) :
    ∑ y : Fin 3, ternaryMass a f V y = 1 := by
  simp [Fin.sum_univ_succ, ternaryMass]
  field_simp [ha]
  ring

theorem ternary_mean (a f V ) (ha : a ≠ 0) :
    ternaryExpectation a f V id = f := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

theorem ternary_variance (a f V ) (ha : a ≠ 0) :
    ternaryExpectation a f V (fun y => (y - f) ^ 2) = V := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

/-- The exact centered fourth moment appearing in the paper. -/
theorem ternary_fourth_central_moment (a f V ) (ha : a ≠ 0) :
    ternaryExpectation a f V (fun y => (y - f) ^ 4) =
      a ^ 2 * V + (6 * V - 3 * a ^ 2) * f ^ 2 + 3 * f ^ 4 := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

/-- Explicit sufficient conditions for all masses to be strictly positive. -/
theorem ternary_mass_positive (a f V ) (ha : 0 < a)
    (hupper : V + f ^ 2 < a ^ 2)
    (hlower : a * |f| < V + f ^ 2) :
    ∀ y, 0 < ternaryMass a f V y := by
  have  := mul_le_mul_of_nonneg_left (le_abs_self f) ha.le
  have : -a * f ≤ a * |f| := by
    have := mul_le_mul_of_nonneg_left (neg_le_abs f) ha.le
    nlinarith
  intro y
  fin_cases y
  · exact div_pos (by linarith) (by positivity)
  · dsimp [ternaryMass]
    exact sub_pos.mpr ((div_lt_one (sq_pos_of_pos ha)).mpr hupper)
  · exact div_pos (by linarith) (by positivity)

/-- Every nonnegative normalized mass is at most one. -/
theorem ternary_mass_le_one (a f V ) (ha : a ≠ 0)
    (hnonneg : ∀ y, 0 ≤ ternaryMass a f V y) (y ) :
    ternaryMass a f V y ≤ 1 := by
  rw [← ternary_normalized a f V ha]
  exact Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ y)

/-- The mass derivative in the variance direction. -/
def ternaryVarianceDerivative (a : ℝ) : Fin 3 → ℝ :=
  ![1 / (2 * a ^ 2), -1 / a ^ 2, 1 / (2 * a ^ 2)]

/-- The mass derivative in the regression direction. -/
def ternaryMeanDerivative (a f : ℝ) : Fin 3 → ℝ :=
  ![(2 * f - a) / (2 * a ^ 2), -(2 * f) / a ^ 2,
    (2 * f + a) / (2 * a ^ 2)]

/-- The second mass derivative in the regression direction. -/
def ternaryMeanSecondDerivative (a : ℝ) : Fin 3 → ℝ :=
  ![1 / a ^ 2, -2 / a ^ 2, 1 / a ^ 2]

/-- The displayed variance derivative is the actual derivative of every mass. -/
theorem ternary_hasDerivAt_variance (a f V y) :
    HasDerivAt (fun W => ternaryMass a f W y) (ternaryVarianceDerivative a y) V := by
  fin_cases y
  · change HasDerivAt (fun W => (W + f ^ 2 - a * f) / (2 * a ^ 2))
      (1 / (2 * a ^ 2)) V
    exact ((((hasDerivAt_id V).add_const (f ^ 2)).sub_const (a * f)).div_const
      (2 * a ^ 2)).congr_deriv (by ring)
  · change HasDerivAt (fun W => 1 - (W + f ^ 2) / a ^ 2) (-1 / a ^ 2) V
    exact ((hasDerivAt_const V 1).sub
      (((hasDerivAt_id V).add_const (f ^ 2)).div_const (a ^ 2))).congr_deriv (by ring)
  · change HasDerivAt (fun W => (W + f ^ 2 + a * f) / (2 * a ^ 2))
      (1 / (2 * a ^ 2)) V
    exact ((((hasDerivAt_id V).add_const (f ^ 2)).add_const (a * f)).div_const
      (2 * a ^ 2)).congr_deriv (by ring)

/-- The displayed regression derivative is the actual derivative. -/
theorem ternary_hasDerivAt_mean (a f V y) :
    HasDerivAt (fun g => ternaryMass a g V y) (ternaryMeanDerivative a f y) f := by
  fin_cases y
  · change HasDerivAt (fun g => (V + g ^ 2 - a * g) / (2 * a ^ 2))
      ((2 * f - a) / (2 * a ^ 2)) f
    exact ((((hasDerivAt_const f V).add ((hasDerivAt_id f).pow 2)).sub
      ((hasDerivAt_const f a).mul (hasDerivAt_id f))).div_const
      (2 * a ^ 2)).congr_deriv (by simp only [id_eq]; ring)
  · change HasDerivAt (fun g => 1 - (V + g ^ 2) / a ^ 2) (-(2 * f) / a ^ 2) f
    exact ((hasDerivAt_const f 1).sub
      (((hasDerivAt_const f V).add ((hasDerivAt_id f).pow 2)).div_const
      (a ^ 2))).congr_deriv (by simp only [id_eq]; ring)
  · change HasDerivAt (fun g => (V + g ^ 2 + a * g) / (2 * a ^ 2))
      ((2 * f + a) / (2 * a ^ 2)) f
    exact ((((hasDerivAt_const f V).add ((hasDerivAt_id f).pow 2)).add
      ((hasDerivAt_const f a).mul (hasDerivAt_id f))).div_const
      (2 * a ^ 2)).congr_deriv (by simp only [id_eq]; ring)

/-- The displayed second regression derivative is the actual derivative. -/
theorem ternary_hasDerivAt_mean_derivative (a f y) :
    HasDerivAt (fun g => ternaryMeanDerivative a g y)
      (ternaryMeanSecondDerivative a y) f := by
  fin_cases y
  · change HasDerivAt (fun g => (2 * g - a) / (2 * a ^ 2)) (1 / a ^ 2) f
    exact ((((hasDerivAt_id f).const_mul 2).sub_const a).div_const
      (2 * a ^ 2)).congr_deriv (by simp [div_eq_mul_inv]; ring)
  · change HasDerivAt (fun g => -(2 * g) / a ^ 2) (-2 / a ^ 2) f
    exact (((hasDerivAt_id f).const_mul 2).neg.div_const
      (a ^ 2)).congr_deriv (by ring)
  · change HasDerivAt (fun g => (2 * g + a) / (2 * a ^ 2)) (1 / a ^ 2) f
    exact ((((hasDerivAt_id f).const_mul 2).add_const a).div_const
      (2 * a ^ 2)).congr_deriv (by simp [div_eq_mul_inv]; ring)

/-- The exact heat identity for the quadratic masses. -/
theorem ternary_heat_identity (a y) :
    ternaryMeanSecondDerivative a y = 2 * ternaryVarianceDerivative a y := by
  fin_cases y <;> simp [ternaryMeanSecondDerivative, ternaryVarianceDerivative] <;> ring

end

end NearlyMinimax
