/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorMassInterpolation

/-! The positive weighted Jensen step reducing the annular square to one root. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Unnormalized nonnegative Jensen/Cauchy inequality, retaining all measure endpoints. -/
theorem lintegral_square_le_mass (μ : Measure ℂ) (f : ℂ → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * μ Set.univ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hf.aemeasurable (aemeasurable_const : AEMeasurable (fun _ => (1 : ℝ≥0∞)) μ)
  have hh := pow_le_pow_left' h 2
  rw [mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_two, ← ENNReal.rpow_mul] at hh
  simp_all

/-- Jensen absorbs one inverse order without any hidden finiteness or nonvanishing assumption. -/
theorem jensen_inverse_square_bound (A L J I : ℝ≥0∞) (p : ℝ)
    (hp : 0 ≤ p) (hA : A ^ 2 ≤ J * L) (hL : L ≤ I) :
    A ^ 2 * I ^ (-p - 2) ≤ J * I ^ (-p - 1) := by
  by_cases hI0 : I = 0
  · simp_all
  by_cases hItop : I = ⊤
  · have hneg2 : -p - 2 < 0 := by linarith only [hp]
    simp_all
  have hcombine : I * I ^ (-p - 2) = I ^ (-p - 1) := by
    nth_rw 1 [← ENNReal.rpow_one I]
    rw [← ENNReal.rpow_add 1 _ hI0 hItop]
    ring
  calc
    A ^ 2 * I ^ (-p - 2) ≤ (J * L) * I ^ (-p - 2) := mul_le_mul' hA le_rfl
    _ ≤ (J * I) * I ^ (-p - 2) := mul_le_mul' (mul_le_mul' le_rfl hL) le_rfl
    _ = J * I ^ (-p - 1) := by rw [mul_assoc, hcombine]

end DOZZ.Proofs
