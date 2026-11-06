/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Covariance

/-!
# GaussianFields.LogCorrelated/ABK/TestFunctionAlgebra

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-! ## Pointwise algebraic structure on mean-zero test functions -/

namespace MeanZeroTestFunction

instance {d : Nat} : Add (MeanZeroTestFunction d) where
  add ψ φ :=
    { toFun := fun x => ψ x + φ x
      continuous := ψ.continuous.add φ.continuous
      hasCompactSupport := ψ.hasCompactSupport.add φ.hasCompactSupport
      integrable := ψ.integrable.add φ.integrable
      memLp_two := ψ.memLp_two.add φ.memLp_two
      integral_eq_zero := by
        rw [integral_add ψ.integrable φ.integrable, ψ.integral_eq_zero,
          φ.integral_eq_zero, add_zero] }

instance {d : Nat} : SMul ℝ (MeanZeroTestFunction d) where
  smul c ψ :=
    { toFun := fun x => c • ψ.toFun x
      continuous := ψ.continuous.const_smul c
      hasCompactSupport := by
        have hfun : (fun x : Vec d => c • ψ.toFun x) =
            (fun _ : Vec d => c) • ψ.toFun := by
          funext x
          exact (Pi.smul_apply' x (fun _ : Vec d => c) ψ.toFun).symm
        rw [hfun]
        exact ψ.hasCompactSupport.smul_left (f := fun _ : Vec d => c)
      integrable := by
        simpa only [smul_eq_mul] using ψ.integrable.const_mul c
      memLp_two := ψ.memLp_two.const_smul c
      integral_eq_zero := by
        rw [integral_smul, ψ.integral_eq_zero, smul_zero] }

@[simp]
theorem add_apply {d} (ψ φ : MeanZeroTestFunction d) x :
    (ψ + φ) x = ψ x + φ x := rfl

@[simp]
theorem smul_apply {d : Nat} (c : ℝ) (ψ : MeanZeroTestFunction d) (x : Vec d) :
    (c • ψ) x = c • ψ x := rfl

end MeanZeroTestFunction

/-! ## Linearity of the ABK spatial convolution -/



/-! ## Linearity of the deterministic ABK kernels -/





/-! ## Linearity of the `L²` kernel vectors -/

theorem abkLogKernelLp_add {d} normalization (ζ : ABKCutoff d)
    (ψ φ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkLogKernelProd normalization ζ φ) 2
        (volume : Measure (ℝ × Vec d)))
    (hsum :
      MemLp (abkLogKernelProd normalization ζ (ψ + φ)) 2
        (volume : Measure (ℝ × Vec d))) :
    abkLogKernelLp normalization ζ (ψ + φ) hsum =
      abkLogKernelLp normalization ζ ψ hψ +
        abkLogKernelLp normalization ζ φ hφ := by
  have abkLogKernel_add : abkLogKernel normalization ζ (ψ + φ) = abkLogKernel normalization ζ ψ + abkLogKernel normalization ζ φ := by
    have abkLogKernelProd_add {d} normalization (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (φ : MeanZeroTestFunction d) : abkLogKernelProd normalization ζ (ψ + φ) = abkLogKernelProd normalization ζ ψ + abkLogKernelProd normalization ζ φ := by
      have abkSpatialConvolution_add {d} (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (φ : MeanZeroTestFunction d) r y : abkSpatialConvolution ζ (ψ + φ) r y = abkSpatialConvolution ζ ψ r y + abkSpatialConvolution ζ φ r y := by
        unfold abkSpatialConvolution
        rw [← integral_add (integrable_abkSpatialConvolution_integrand ζ ψ r y)
          (integrable_abkSpatialConvolution_integrand ζ φ r y)]
        refine integral_congr_ae ?_
        filter_upwards with x
        simp [mul_add]
      funext p
      by_cases hp : 0 < p.1
      · simp [abkLogKernelProd, hp, abkSpatialConvolution_add, mul_add]
      · simp [abkLogKernelProd, hp]
    funext z
    simp [abkLogKernel, abkLogKernelProd_add]
  unfold abkLogKernelLp
  rw [← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _
    (Filter.EventuallyEq.of_eq (abkLogKernel_add))

theorem abkLogKernelLp_smul {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d)
    (c : ℝ) (ψ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hsmul :
      MemLp (abkLogKernelProd normalization ζ (c • ψ)) 2
        (volume : Measure (ℝ × Vec d))) :
    abkLogKernelLp normalization ζ (c • ψ) hsmul =
      c • abkLogKernelLp normalization ζ ψ hψ := by
  have abkLogKernel_smul : abkLogKernel normalization ζ (c • ψ) = c • abkLogKernel normalization ζ ψ := by
    have abkLogKernelProd_smul {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d) (c : ℝ) (ψ : MeanZeroTestFunction d) : abkLogKernelProd normalization ζ (c • ψ) = c • abkLogKernelProd normalization ζ ψ := by
      have abkSpatialConvolution_smul {d : Nat} (ζ : ABKCutoff d) (c : ℝ) (ψ : MeanZeroTestFunction d) r y : abkSpatialConvolution ζ (c • ψ) r y = c * abkSpatialConvolution ζ ψ r y := by
        unfold abkSpatialConvolution
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards with x
        simp only [MeanZeroTestFunction.smul_apply, smul_eq_mul]
        ring
      funext p
      by_cases hp : 0 < p.1
      · simp only [abkLogKernelProd, ite_eq_left hp, abkSpatialConvolution_smul,
          Pi.smul_apply, smul_eq_mul]
        ring
      · simp [abkLogKernelProd, hp]
    funext z
    simp [abkLogKernel, abkLogKernelProd_smul]
  unfold abkLogKernelLp
  rw [← MemLp.toLp_const_smul]
  exact MemLp.toLp_congr _ _
    (Filter.EventuallyEq.of_eq (abkLogKernel_smul))

end GaussianFields

end
