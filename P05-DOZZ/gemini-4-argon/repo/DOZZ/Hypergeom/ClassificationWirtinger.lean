/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.WirtingerZ
public import DOZZ.Statements.Hypergeom.IsRealGaussSolution
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! First-order calculus rules for the Wirtinger derivative. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

/-- The Wirtinger derivative obeys the ordinary product rule for real-differentiable
complex-valued functions. -/
theorem wirtingerZ_mul {f g : ℂ → ℂ} {z}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerZ (fun w => f w * g w) z =
      f z * wirtingerZ g z + g z * wirtingerZ f z := by
  rw [wirtingerZ, wirtingerZ, wirtingerZ, fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply]
  ring

/-- The Wirtinger derivative is additive on functions differentiable at the point. -/
theorem wirtingerZ_add {f g : ℂ → ℂ} {z}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerZ (fun w => f w + g w) z = wirtingerZ f z + wirtingerZ g z := by
  rw [wirtingerZ, wirtingerZ, wirtingerZ, (show fderiv ℝ (fun w => f w + g w) z = fderiv ℝ f z + fderiv ℝ g z by exact fderiv_add hf hg)]
  simp only [add_apply]
  ring

/-- On a complex-differentiable function, the Wirtinger derivative is the ordinary complex
derivative. -/
theorem wirtingerZ_eq_deriv_of_differentiableAt {f : ℂ → ℂ} {z}
    (hf : DifferentiableAt ℂ f z) :
    wirtingerZ f z = deriv f z := by
  have hCR := (differentiableAt_complex_iff_differentiableAt_real.mp hf).2
  rw [wirtingerZ, (show fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1 by simpa only [smul_eq_mul] using hCR), complexOfReal_deriv (hf.restrictScalars ℝ) hCR]
  rw [← mul_assoc, Complex.I_mul_I]
  ring

/-- The Wirtinger derivative annihilates the conjugate of a holomorphic function. -/
theorem wirtingerZ_star_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z}
    (hf : DifferentiableAt ℂ f z) :
    wirtingerZ (fun w => star (f w)) z = 0 := by
  rw [wirtingerZ, fderiv_star]
  simp only [ContinuousLinearMap.comp_apply]
  change (star (fderiv ℝ f z 1) -
      Complex.I * star (fderiv ℝ f z Complex.I)) / 2 = 0
  rw [(show fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1 by simpa only [smul_eq_mul] using ((differentiableAt_complex_iff_differentiableAt_real.mp hf).2))]
  rw [star_mul]
  simp only [Complex.star_def, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- A holomorphic times antiholomorphic tensor has the expected `z`-derivative. -/
theorem wirtingerZ_mul_star_of_differentiableAt {f g : ℂ → ℂ} {z}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    wirtingerZ (fun w => f w * star (g w)) z =
      star (g z) * deriv f z := by
  rw [wirtingerZ_mul (hf.restrictScalars ℝ) ((hg.restrictScalars ℝ).star),
    wirtingerZ_star_eq_zero_of_differentiableAt hg,
    wirtingerZ_eq_deriv_of_differentiableAt hf]
  simp

/-- The Wirtinger derivative is unchanged when two functions agree near the evaluation point. -/
theorem wirtingerZ_congr_of_eventuallyEq {f g : ℂ → ℂ} {z}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (hfg : f =ᶠ[𝓝 z] g) :
    wirtingerZ f z = wirtingerZ g z := by
  rw [wirtingerZ, wirtingerZ, (show fderiv ℝ f z = fderiv ℝ g z by exact (hfg.hasFDerivAt_iff.mp hf.hasFDerivAt).unique hg.hasFDerivAt)]

end DOZZ.Proofs
