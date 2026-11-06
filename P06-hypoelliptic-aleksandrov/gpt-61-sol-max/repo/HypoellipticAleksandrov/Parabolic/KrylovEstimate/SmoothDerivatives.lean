module

public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine

open private HypoellipticAleksandrov.Parabolic.KrylovEstimate.coordinate_single_smooth from HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine


/-! # Selected scalar and joint derivatives agree on smooth functions -/

 public section

namespace HypoellipticAleksandrov.Parabolic.KrylovEstimate



variable {N : ℕ} (w : HypoellipticAleksandrov.Parabolic.ScalarField N) (hw : ContDiff ℝ 2 w)




variable (z : TimeVelocity N)

include hw
/-- The scalar time derivative equals the joint directional derivative. -/
theorem scalarTimeDerivative_eq_timeDerivative
      :
    scalarTimeDerivative w z = timeDerivative w z := by
  rw [scalarTimeDerivative_eq_coordinateIteratedFDeriv_of_contDiff_two hw z,
    _root_.HypoellipticAleksandrov.Parabolic.KrylovEstimate.coordinate_single_smooth w hw]
  rfl
/-- The scalar gradient equals the joint velocity gradient. -/
theorem scalarSpatialGradient_eq_velocityGradient
      :
    scalarSpatialGradient w z = velocityGradient w z := by
  ext i
  rw [scalarSpatialGradient_apply_eq_coordinateIteratedFDeriv_of_contDiff_two hw z i,
    _root_.HypoellipticAleksandrov.Parabolic.KrylovEstimate.coordinate_single_smooth w hw]
  rfl

/-- The scalar Hessian equals the joint velocity Hessian. -/
theorem scalarSpatialHessian_eq_velocityHessian
      :
    scalarSpatialHessian w z = velocityHessian w z := by
  ext i j
  rw [scalarSpatialHessian_apply_eq_coordinateIteratedFDeriv_of_contDiff_two hw z i j]

  have hs := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
    (Pi.single (velocityCoord j) 1) (velocityCoord i) w z (by
      simpa only [TimeVelocityMultiIndex.order_single, Nat.cast_one,
        show (1 : WithTop ℕ∞) + 1 = 2 from rfl] using! hw.contDiffAt)
  have hf : TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (Pi.single (velocityCoord j) 1) w =
      (fun y => fderiv ℝ w y (timeVelocityBasis (velocityCoord j))) := by
    funext y
    exact _root_.HypoellipticAleksandrov.Parabolic.KrylovEstimate.coordinate_single_smooth w hw _ y
  rw [hs, hf]
  have hd := ((hw.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num)) z
  rw [fderiv_clm_apply hd (differentiableAt_const (c :=
    timeVelocityBasis (velocityCoord j)))]
  simp [timeVelocityBasis_velocity, velocityHessian, PDE.basisVec]

end HypoellipticAleksandrov.Parabolic.KrylovEstimate
