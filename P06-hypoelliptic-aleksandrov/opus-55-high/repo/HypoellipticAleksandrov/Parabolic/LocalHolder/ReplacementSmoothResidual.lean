module

public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
public import HypoellipticAleksandrov.Coefficients.Ellipticity

/-! # Smooth forcing of smooth ambient boundary extensions

The first time and second spatial derivatives retain infinite differentiability.
-/

@[expose] public section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open TimeVelocityMultiIndex
open scoped Matrix.Norms.Elementwise

variable {d : ℕ} (w : TimeVelocity d → ℝ)

/-- Every finite coordinate derivative of an infinitely differentiable function is smooth. -/
theorem contDiff_coordinateIteratedFDeriv_infty 
    (alpha : TimeVelocityMultiIndex d) (w : TimeVelocity d → ℝ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateIteratedFDeriv alpha w) := by
  have hi := hw.iteratedFDeriv_right
    (m := (⊤ : ℕ∞)) (i := alpha.coordinateList.length) (by simp)
  exact (contDiff_const (c := ContinuousMultilinearMap.apply ℝ _ _
    _)).clm_apply hi

/-- The classical time derivative of a smooth ambient extension is smooth. -/
theorem contDiff_scalarTimeDerivative_infty 
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarTimeDerivative w) := by
  have h := contDiff_coordinateIteratedFDeriv_infty (Pi.single (timeCoord d) 1) w hw
  have heq : scalarTimeDerivative w =
      coordinateIteratedFDeriv _ w :=
    funext (scalarTimeDerivative_eq_coordinateIteratedFDeriv_of_contDiff_two
      (hw.of_le (by simp)))
  simp_all

/-- Every Hessian entry of a smooth ambient extension is smooth. -/
theorem contDiff_scalarSpatialHessian_entry_infty 
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => scalarSpatialHessian w z i j) := by
  have h := contDiff_coordinateIteratedFDeriv_infty
    (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) w hw
  have heq : (fun z => scalarSpatialHessian w z i j) =
      coordinateIteratedFDeriv
        _ w :=
    funext (fun z => scalarSpatialHessian_apply_eq_coordinateIteratedFDeriv_of_contDiff_two
      (hw.of_le (by simp)) z i j)
  simp_all

/-- The signed backward residual of a smooth ambient extension is an actual smooth source. -/
theorem contDiff_smooth_backward_residual  (A : CoefficientField d)
    (hA : IsSmoothCoefficient A) (w : TimeVelocity d → ℝ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => scalarTimeDerivative w z +
      matrixContraction (coefficientAt A z) (scalarSpatialHessian w z)) := by
  apply (contDiff_scalarTimeDerivative_infty w hw).add
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact ((contDiff_apply ℝ ℝ j).comp
    ((contDiff_apply ℝ _ i).comp hA)).mul
      (contDiff_scalarSpatialHessian_entry_infty w hw i j)

end HypoellipticAleksandrov.Parabolic.LocalHolder
