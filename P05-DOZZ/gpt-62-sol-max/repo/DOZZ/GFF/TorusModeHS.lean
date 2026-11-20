/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusModeTests
public import DOZZ.GFF.TorusFourierSobolev

/-!
# DOZZ.GFF.TorusModeHS

The concrete cutoff trigonometric modes have uniformly bounded covariance energy on each local
box. The reciprocal H² weights make their energy sum finite.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped InnerProductSpace Topology

namespace DOZZ

/-- The local Schur constant for the cutoff trigonometric family on the support ball. -/
noncomputable def localTorusModeEnergyConstant (R : ℝ) : ℝ :=
  (∫ p : ℂ × ℂ in ball (0 : ℂ) (R + 3) ×ˢ ball (0 : ℂ) (R + 3),
    ‖gffKernel p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ) *
      (volume (ball (0 : ℂ) (R + 3))).toReal


private theorem norm_sq_torusTest_le (R : ℝ) (f : TestFn)
    (hs : Function.support f ⊆ ball (0 : ℂ) (R + 3)) (hf : ∀ z, |f z| ≤ 1) (c : ℝ) :
    ‖equatorKernelLimitMap (c • f)‖ ^ 2 ≤ c ^ 2 * localTorusModeEnergyConstant R := by
  rw [map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  refine mul_le_mul_of_nonneg_left ((norm_sq_equatorKernelLimitMap_le_localL2 _ _ hs).trans ?_)
    (sq_nonneg c)
  unfold localTorusModeEnergyConstant
  exact mul_le_mul_of_nonneg_left (torusTest_integral_sq_le_volume R f hf) (by positivity)

private theorem summable_localTorusTestHSEnergy (R : ℝ) (f : (Fin 2 → ℤ) → TestFn)
    (hs : ∀ k, Function.support (f k) ⊆ ball (0 : ℂ) (R + 3)) (hf : ∀ k z, |f k z| ≤ 1) :
    Summable fun k => ‖equatorKernelLimitMap ((torusSobolevWeight k)⁻¹ • f k)‖ ^ 2 := by
  apply Summable.of_nonneg_of_le (fun k => sq_nonneg _) _
    (summable_torusSobolevWeight_inv_sq.mul_right (localTorusModeEnergyConstant R))
  intro k
  exact norm_sq_torusTest_le R _ (hs k) (hf k) _

section
variable (R L : ℝ) (hR : 0 < R)

theorem summable_localTorusCosHSEnergy :
    Summable fun k : Fin 2 → ℤ =>
      ‖equatorKernelLimitMap ((torusSobolevWeight k)⁻¹ • localTorusCosTest R L hR k)‖ ^ 2 :=
  summable_localTorusTestHSEnergy R _ (localTorusCosTest_support_subset R L hR)
    (localTorusCosTest_abs_le_one R L hR)

theorem summable_localTorusSinHSEnergy :
    Summable fun k : Fin 2 → ℤ =>
      ‖equatorKernelLimitMap ((torusSobolevWeight k)⁻¹ • localTorusSinTest R L hR k)‖ ^ 2 :=
  summable_localTorusTestHSEnergy R _ (localTorusSinTest_support_subset R L hR)
    (localTorusSinTest_abs_le_one R L hR)

end

end DOZZ

end
