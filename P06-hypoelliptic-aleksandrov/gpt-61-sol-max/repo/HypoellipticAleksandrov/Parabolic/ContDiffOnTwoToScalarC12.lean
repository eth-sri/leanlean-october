module

public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.C2ToScalarC12
import all HypoellipticAleksandrov.Parabolic.GenericProperCommutatorResidual

open private HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_eq_coordinate_local from HypoellipticAleksandrov.Parabolic.C2ToScalarC12
open private HypoellipticAleksandrov.Parabolic.scalarSpatialGradient_eq_coordinate_local from HypoellipticAleksandrov.Parabolic.C2ToScalarC12
open private HypoellipticAleksandrov.Parabolic.scalarTimeDerivative_eq_coordinate_local from HypoellipticAleksandrov.Parabolic.C2ToScalarC12
open private HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_continuousOn from HypoellipticAleksandrov.Parabolic.GenericProperCommutatorResidual


/-!
# Local C² regularity implies scalar parabolic C¹˒² regularity

This module converts second-order ambient differentiability on an open carrier
into the anisotropic scalar regularity used by the parabolic equation.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic
open Set

section
open TimeVelocityMultiIndex













/-- On an open carrier, ambient `C²` regularity within the carrier implies the
scalar anisotropic `C¹,²` regularity used by the parabolic equation. -/
theorem isScalarC12On_of_isOpen_contDiffOn_two
    {d : ℕ} {Q : HypoellipticAleksandrov.Parabolic.Region d} {w : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hQ : IsOpen Q) (hw : ContDiffOn ℝ 2 w Q) :
    IsScalarC12On w Q := by
  refine ⟨hw.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (((hw.contDiffAt (hQ.mem_nhds hz)).differentiableAt
      (by norm_num)).hasFDerivAt.comp z.1
        ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).differentiableAt
  · intro z hz
    exact (hw.contDiffAt (hQ.mem_nhds hz)).comp z.2
      (contDiffAt_const.prodMk contDiffAt_id)
  · apply ContinuousOn.congr
      (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_continuousOn hQ w hw
        (Pi.single (timeCoord d) 1) (by
          simp_all))
    intro z hz
    exact _root_.HypoellipticAleksandrov.Parabolic.scalarTimeDerivative_eq_coordinate_local w z
      ((hw.contDiffAt (hQ.mem_nhds hz)).of_le (by norm_num))
  · rw [continuousOn_pi]
    intro j
    apply ContinuousOn.congr
      (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_continuousOn hQ w hw
        (Pi.single (velocityCoord j) 1) (by
          simp_all))
    intro z hz
    exact _root_.HypoellipticAleksandrov.Parabolic.scalarSpatialGradient_eq_coordinate_local w z j
      ((hw.contDiffAt (hQ.mem_nhds hz)).of_le (by norm_num))
  · apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    apply ContinuousOn.congr
      (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_continuousOn hQ w hw
        (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) (by
          simp_all))
    intro z hz
    exact _root_.HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_eq_coordinate_local w z i j
      (hw.contDiffAt (hQ.mem_nhds hz))

end
end HypoellipticAleksandrov.Parabolic
