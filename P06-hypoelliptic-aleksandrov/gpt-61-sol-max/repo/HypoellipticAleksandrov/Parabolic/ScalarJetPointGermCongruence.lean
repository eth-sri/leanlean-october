module

public import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.C2ToScalarC12

open private HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_eq_coordinate_local from HypoellipticAleksandrov.Parabolic.C2ToScalarC12
open private HypoellipticAleksandrov.Parabolic.scalarSpatialGradient_eq_coordinate_local from HypoellipticAleksandrov.Parabolic.C2ToScalarC12
open private HypoellipticAleksandrov.Parabolic.scalarTimeDerivative_eq_coordinate_local from HypoellipticAleksandrov.Parabolic.C2ToScalarC12


/-!
# Scalar jets of equal point germs

This module proves that ambient C² functions agreeing near a point have equal
scalar time, gradient, and ordered Hessian jets at that point.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic
open Filter

section
open TimeVelocityMultiIndex

variable {d : ℕ}










/-- Two ambient `C²` germs that agree near a point have the same scalar time,
gradient, and ordered Hessian jets at that point. -/
theorem scalarJet_eqAt_of_eventuallyEq
     {f g : HypoellipticAleksandrov.Parabolic.ScalarField d} {z : TimeVelocity d}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (hfg : f =ᶠ[nhds z] g) :
    scalarTimeDerivative f z = scalarTimeDerivative g z ∧
    scalarSpatialGradient f z = scalarSpatialGradient g z ∧
    scalarSpatialHessian f z = scalarSpatialHessian g z := by
  constructor
  · rw [_root_.HypoellipticAleksandrov.Parabolic.scalarTimeDerivative_eq_coordinate_local f z (hf.of_le (by norm_num)),
      _root_.HypoellipticAleksandrov.Parabolic.scalarTimeDerivative_eq_coordinate_local g z (hg.of_le (by norm_num))]
    exact coordinateIteratedFDeriv_congr_of_eventuallyEq
      _ hfg
  constructor
  · funext j
    rw [_root_.HypoellipticAleksandrov.Parabolic.scalarSpatialGradient_eq_coordinate_local f z j (hf.of_le (by norm_num)),
      _root_.HypoellipticAleksandrov.Parabolic.scalarSpatialGradient_eq_coordinate_local g z j (hg.of_le (by norm_num))]
    exact coordinateIteratedFDeriv_congr_of_eventuallyEq
      _ hfg
  · funext i j
    rw [_root_.HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_eq_coordinate_local f z i j hf,
      _root_.HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_eq_coordinate_local g z i j hg]
    exact coordinateIteratedFDeriv_congr_of_eventuallyEq
      _ hfg

end
end HypoellipticAleksandrov.Parabolic
