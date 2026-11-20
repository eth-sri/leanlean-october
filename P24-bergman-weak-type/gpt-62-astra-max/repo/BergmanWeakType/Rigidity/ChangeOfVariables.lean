/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

public section

open Set MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

/-- A complex derivative scales real area by its squared norm. -/
theorem det_complex_derivative (c : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

variable {U : Set ℂ} {φ : ℂ → ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    (hinj : InjOn φ U) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

include hU hφ
private theorem realFDeriv {w : ℂ} (hw : w ∈ U) : HasFDerivWithinAt φ
    ((ContinuousLinearMap.toSpanSingleton ℂ (deriv φ w)).restrictScalars ℝ) U w :=
  ((hφ.differentiableAt (hU.mem_nhds hw)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt

include hinj
theorem area_image_eq_map : area.restrict (φ '' U) = Measure.map φ
    ((area.restrict U).withDensity fun w ↦ ENNReal.ofReal (‖deriv φ w‖ ^ 2)) := by
  simpa [det_complex_derivative] using (map_withDensity_abs_det_fderiv_eq_addHaar area
    hU.measurableSet.nullMeasurableSet (fun _ ↦ realFDeriv hU hφ) hinj).symm

theorem area_integral_image_eq (g : ℂ → E) :
    ∫ z in φ '' U, g z ∂area = ∫ w in U, ‖deriv φ w‖ ^ 2 • g (φ w) ∂area := by
  simpa [det_complex_derivative] using integral_image_eq_integral_abs_det_fderiv_smul area
    hU.measurableSet (fun _ ↦ realFDeriv hU hφ) hinj g

theorem area_integrableOn_image_iff_norm_deriv_sq (g : ℂ → E) :
    IntegrableOn g (φ '' U) area ↔ IntegrableOn (fun w ↦ ‖deriv φ w‖ ^ 2 • g (φ w)) U area := by
  simpa [det_complex_derivative] using integrableOn_image_iff_integrableOn_abs_det_fderiv_smul area
    hU.measurableSet (fun _ ↦ realFDeriv hU hφ) hinj g

end BergmanWeakType
