/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Measure
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace BergmanWeakType

/-- A complex derivative scales real area by its squared norm. -/
theorem det_complex_derivative (c : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

private theorem hasFDerivWithinAt_real {U : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) {w : ℂ} (hw : w ∈ U) :
    HasFDerivWithinAt φ ((ContinuousLinearMap.toSpanSingleton ℂ (deriv φ w)).restrictScalars ℝ) U w :=
  ((hφ.differentiableAt (hU.mem_nhds hw)).hasDerivAt.hasFDerivAt
    |>.restrictScalars ℝ).hasFDerivWithinAt

theorem area_integral_image_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (g : ℂ → E) :
    ∫ z in φ '' U, g z ∂area = ∫ w in U, (‖deriv φ w‖ ^ 2 : ℝ) • g (φ w) ∂area := by
  simpa only [det_complex_derivative, abs_sq] using integral_image_eq_integral_abs_det_fderiv_smul
    area hU.measurableSet (fun w ↦ hasFDerivWithinAt_real hU hφ) hinj g

theorem area_integrableOn_image_iff_norm_deriv_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (g : ℂ → E) :
    IntegrableOn g (φ '' U) area ↔
      IntegrableOn (fun w ↦ (‖deriv φ w‖ ^ 2 : ℝ) • g (φ w)) U area := by
  simpa only [det_complex_derivative, abs_sq] using integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    area hU.measurableSet (fun w ↦ hasFDerivWithinAt_real hU hφ) hinj g

end BergmanWeakType
