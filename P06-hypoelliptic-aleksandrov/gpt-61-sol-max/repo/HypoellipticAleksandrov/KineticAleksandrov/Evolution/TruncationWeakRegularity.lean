module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.StraightenedTransferClassical
public import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Joint first differentiability of scalar C1,2 solutions

Continuous time and spatial partial derivatives give joint first differentiability.
No second time or mixed derivative is required.
-/

 public section

open Set HypoellipticAleksandrov.Parabolic


namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The joint first derivative of an anisotropic scalar C1,2 function. -/
theorem scalarC12_hasFDerivAt {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hU : IsOpen U) (hu : IsScalarC12On u U)
    {z : TimeVelocity d} (hz : z ∈ U) :
    HasFDerivAt u
      (((ContinuousLinearMap.id ℝ ℝ).smulRight (scalarTimeDerivative u z)).coprod
        (fderiv ℝ (fun y => u (z.1, y)) z.2)) z := by
  let T (t : ℝ) (x : PDE.Vec d)  :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (scalarTimeDerivative u (t, x))
  let S (t : ℝ) (x : PDE.Vec d) := fderiv ℝ (fun y => u (t, y)) x




  exact (hasStrictFDerivAt_uncurry_coprod
    (f := fun t x => u (t, x)) (f₁ := T) (f₂ := S) (u := z) (by
        filter_upwards [hU.mem_nhds hz] with q hq
        exact (hu.timeSlice_hasDerivAt hq).hasFDerivAt) (by
        filter_upwards [hU.mem_nhds hz] with q hq
        exact ((hu.spatialSlice_contDiffAt hq).differentiableAt (by norm_num)).hasFDerivAt)
    ((show ContinuousOn (fun q : TimeVelocity d => T q.1 q.2) U by
        apply continuousOn_clm_apply.mpr
        intro w
        exact (continuousOn_const.mul hu.continuousOn_scalarTimeDerivative)).continuousAt (hU.mem_nhds hz)) ((show ContinuousOn (fun q : TimeVelocity d => S q.1 q.2) U by
        apply continuousOn_clm_apply.mpr
        intro w
        have he : (fun q : TimeVelocity d => S q.1 q.2 w) =
            fun q => PDE.vecDot (scalarSpatialGradient u q) w := by
          funext q
          exact PDE.fderiv_apply_eq_vecDot_classicalGradient _ _ _
        rw [he]
        unfold PDE.vecDot
        exact continuousOn_finsetSum _ fun i _ =>
          ((continuous_apply i).comp_continuousOn hu.continuousOn_scalarSpatialGradient).mul
            continuousOn_const).continuousAt (hU.mem_nhds hz))).hasFDerivAt

/-- An anisotropic scalar C1,2 function on an open set is jointly differentiable. -/
theorem scalarC12_differentiableAt {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hU : IsOpen U) (hu : IsScalarC12On u U)
    {z : TimeVelocity d} (hz : z ∈ U) : DifferentiableAt ℝ u z :=
  (scalarC12_hasFDerivAt hU hu hz).differentiableAt

end HypoellipticAleksandrov.KineticAleksandrov
