module

public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine

/-! # Selected scalar and joint derivatives agree on smooth functions -/

@[expose] public section
namespace HypoellipticAleksandrov.Parabolic.KrylovEstimate
open Filter
open scoped Topology

variable {N : ℕ} (w : TimeVelocity N → ℝ)


/-- The scalar time derivative equals the joint directional derivative. -/
theorem scalarTimeDerivative_eq_timeDerivative
     (hw : ContDiff ℝ 2 w) (z : TimeVelocity N) :
    scalarTimeDerivative w z = timeDerivative w z := by
  rw [scalarTimeDerivative_eq_coordinateIteratedFDeriv_of_contDiff_two hw,
    coordinate_single_smooth w hw]
  rfl
/-- The scalar gradient equals the joint velocity gradient. -/
theorem scalarSpatialGradient_eq_velocityGradient
     (hw : ContDiff ℝ 2 w) (z : TimeVelocity N) :
    scalarSpatialGradient w z = velocityGradient w z := by
  ext i
  rw [scalarSpatialGradient_apply_eq_coordinateIteratedFDeriv_of_contDiff_two hw,
    coordinate_single_smooth w hw]
  rfl

/-- The scalar Hessian equals the joint velocity Hessian. -/
theorem scalarSpatialHessian_eq_velocityHessian
     (hw : ContDiff ℝ 2 w) (z : TimeVelocity N) :
    scalarSpatialHessian w z = velocityHessian w z := by
  ext i j
  rw [scalarSpatialHessian_apply_eq_coordinateIteratedFDeriv_of_contDiff_two hw]
  have hs := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
    (Pi.single (velocityCoord j) 1) (velocityCoord i) w z (by
      simpa using! hw.contDiffAt)
  have hf : TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (Pi.single (velocityCoord j) 1) w =
      (fun y => fderiv ℝ w y (timeVelocityBasis (velocityCoord j))) := by
    funext y
    exact coordinate_single_smooth w hw _ y
  rw [hs, hf]
  have hd := ((hw.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num)) z
  rw [fderiv_clm_apply hd (differentiableAt_const (c :=
    timeVelocityBasis _))]
  aesop

end HypoellipticAleksandrov.Parabolic.KrylovEstimate
