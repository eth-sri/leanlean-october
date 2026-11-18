/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.WirtingerZ
public import DOZZ.Hypergeom.ClassificationWirtinger
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! First-order regularity and Cauchy--Riemann consequences for the Wirtinger operator. -/

@[expose] public section

namespace DOZZ.Proofs

variable {f : ℂ → ℂ} {z : ℂ}


/-- The Wirtinger derivative of a twice continuously real-differentiable function is
once continuously real-differentiable. -/
theorem differentiableAt_wirtingerZ_of_contDiffAt_two
 (hf : ContDiffAt ℝ 2 f z) :
    DifferentiableAt ℝ (fun w => wirtingerZ f w) z := by
  have :=
    hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hnum : ContDiffAt ℝ 1
      (fun w => fderiv ℝ f w 1 - Complex.I * fderiv ℝ f w Complex.I) z := by fun_prop
  simpa only [wirtingerZ] using (hnum.div_const 2).differentiableAt (by norm_num)

/-- If the `∂z` derivative of a real-differentiable complex-valued function vanishes,
then its complex conjugate is complex-differentiable at that point. -/
theorem differentiableAt_star_of_wirtingerZ_eq_zero
 (hf : DifferentiableAt ℝ f z)
    (hzero : wirtingerZ f z = 0) :
    DifferentiableAt ℂ (fun w => star (f w)) z := by
  apply (differentiableAt_complex_iff_differentiableAt_real).2
  refine ⟨hf.star, ?_⟩
  have hzero' :
      (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) / 2 = 0 := by assumption
  have hrel : fderiv ℝ f z Complex.I = -Complex.I * fderiv ℝ f z 1 := by
    have hsub : fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I = 0 := by
      linear_combination (congrArg (fun x : ℂ => x * 2) hzero')
    have hsub' :=
      sub_eq_zero.mp hsub
    calc
      fderiv ℝ f z Complex.I = -(Complex.I * Complex.I) *
          fderiv ℝ f z Complex.I := by rw [Complex.I_mul_I]; simp
      _ = -Complex.I * (Complex.I * fderiv ℝ f z Complex.I) := by ring
      _ = -Complex.I * fderiv ℝ f z 1 := by rw [← hsub']
  rw [fderiv_star]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hrel]
  simp [smul_eq_mul]

/-- The Wirtinger derivative is additive for differences of real-differentiable maps. -/
theorem wirtingerZ_sub {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerZ (fun w => f w - g w) z = wirtingerZ f z - wirtingerZ g z := by
  have hneg := wirtingerZ_mul (differentiableAt_const (-1 : ℂ)) hg
  have hnegFun : (fun w => (-1 : ℂ) * g w) = fun w => -g w := by ring
  rw [hnegFun] at hneg
  have hneg' : wirtingerZ (fun w => -g w) z = -wirtingerZ g z := by
    simpa [wirtingerZ] using hneg
  have hadd := wirtingerZ_add hf hg.neg
  have hneg'' : wirtingerZ (-g) z = -wirtingerZ g z := by assumption
  have : (fun w => f w + (-g) w) = (fun w => f w + -g w) := by rfl
  have hadd' : wirtingerZ (fun w => f w + -g w) z =
      wirtingerZ f z - wirtingerZ g z := by grind
  assumption

/-- On a complex-differentiable nonvanishing denominator, the `∂z` derivative of its
reciprocal is the ordinary reciprocal derivative. -/
theorem wirtingerZ_inv_of_differentiableAt
 (hf : DifferentiableAt ℂ f z) (hzero : f z ≠ 0) :
    wirtingerZ (fun w => (f w)⁻¹) z = -(f z)⁻¹ ^ 2 * deriv f z := by
  have hInv : DifferentiableAt ℂ (fun w => (f w)⁻¹) z := hf.inv hzero
  rw [wirtingerZ_eq_deriv_of_differentiableAt hInv]
  calc
    _ = deriv f⁻¹ z := rfl
    _ = -deriv f z / f z ^ 2 := (hf.hasDerivAt.inv hzero).deriv
    _ = -(f z)⁻¹ ^ 2 * deriv f z := by ring

end DOZZ.Proofs
