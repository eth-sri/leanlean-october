module

public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12

/-!
# Local C² regularity implies scalar parabolic C¹˒² regularity

This module converts second-order ambient differentiability on an open carrier
into the anisotropic scalar regularity used by the parabolic equation.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic
open Set
open scoped Topology
noncomputable section
open TimeVelocityMultiIndex

section
variable {d : ℕ} (u : TimeVelocity d → ℝ) (z : TimeVelocity d) (j : Fin d)
    (hu : ContDiffAt ℝ 1 u z)

include hu in
private theorem scalarTimeDerivative_eq_coordinate_open_local :
    scalarTimeDerivative u z =
      coordinateIteratedFDeriv (Pi.single (timeCoord d) 1) u z := by
  have h := coordinateIteratedFDeriv_add_single_at
    0 (timeCoord d) u z
      (by simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
        TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity] using hu)
  simp only [zero_add, timeVelocityBasis_time] at h
  rw [show coordinateIteratedFDeriv 0 u = u by
    funext x; apply coordinateIteratedFDeriv_zero] at h
  rw [h]
  unfold scalarTimeDerivative
  have hsF := (hu.differentiableAt (by norm_num)).hasFDerivAt.comp z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  have hs : HasDerivAt (fun r : ℝ ↦ u (r, z.2))
      ((fderiv ℝ u z) (1, 0)) z.1 := by
    convert hsF.hasDerivAt using 1
    all_goals simp [Function.comp_def]
  exact hs.deriv

include hu in
private theorem scalarSpatialGradient_eq_coordinate_open_local :
    scalarSpatialGradient u z j =
      coordinateIteratedFDeriv (Pi.single (velocityCoord j) 1) u z := by
  have h := coordinateIteratedFDeriv_add_single_at
    0 (velocityCoord j) u z
      (by simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
        TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity] using hu)
  simp only [zero_add, timeVelocityBasis_velocity] at h
  rw [show coordinateIteratedFDeriv 0 u = u by
    funext x; apply coordinateIteratedFDeriv_zero] at h
  rw [h, scalarSpatialGradient, PDE.classicalGradient_apply]
  have hs : HasFDerivAt (fun y : PDE.Vec d ↦ u (z.1, y))
      ((fderiv ℝ u z).comp (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d))) z.2 :=
    (hu.differentiableAt (by norm_num)).hasFDerivAt.comp z.2
      ((hasFDerivAt_const (x := z.2) z.1).prodMk (hasFDerivAt_id z.2))
  rw [hs.fderiv]
  simp

private theorem scalarSpatialHessian_eq_coordinate_open_local (i j : Fin d)
    (hu : ContDiffAt ℝ 2 u z) :
    scalarSpatialHessian u z i j =
      coordinateIteratedFDeriv
        (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) u z := by
  classical
  let q :=
    coordinateIteratedFDeriv (Pi.single (velocityCoord j) 1) u
  have hq : ContDiffAt ℝ 1 q z := by
    apply ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [hu.eventually (by simp)] with x hx
    have hadd := coordinateIteratedFDeriv_add_single_at
      0 (velocityCoord j) u x
      (by simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
        TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity] using
        hx.of_le (by norm_num))
    rw [show coordinateIteratedFDeriv 0 u = u by
      funext y; apply coordinateIteratedFDeriv_zero] at hadd
    simpa using hadd
  have hgradient : (fun x : TimeVelocity d ↦ scalarSpatialGradient u x j) =ᶠ[nhds z] q := by
    filter_upwards [hu.eventually (by simp)] with x hx
    exact scalarSpatialGradient_eq_coordinate_open_local u x j (hx.of_le (by norm_num))
  have hgradientDiff :=
    hgradient.differentiableAt_iff.mpr (hq.differentiableAt (by norm_num))
  have hslice :=
    hu.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)
  have hgradientApply :
      (fderiv ℝ (fun y : PDE.Vec d ↦
          PDE.classicalGradient (fun w : PDE.Vec d ↦ u (z.1, w)) y j) z.2)
          (PDE.basisVec i) =
        (fderiv ℝ (fun y : PDE.Vec d ↦
          PDE.classicalGradient (fun w : PDE.Vec d ↦ u (z.1, w)) y) z.2
          (PDE.basisVec i)) j := by
    have hgrad : DifferentiableAt ℝ
        (fun y ↦ PDE.classicalGradient (fun w : PDE.Vec d ↦ u (z.1, w)) y) z.2 := by
      apply differentiableAt_pi.2
      intro k
      exact ((hslice.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply (differentiableAt_const (c := PDE.basisVec k))
    rw [fderiv_pi (fun k ↦ (differentiableAt_pi.mp hgrad) k)]
    simp
  have hcomp :
      fderiv ℝ (fun y : PDE.Vec d ↦ scalarSpatialGradient u (z.1, y) j) z.2 =
        (fderiv ℝ (fun x : TimeVelocity d ↦ scalarSpatialGradient u x j) z).comp
          (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d)) := by
    change fderiv ℝ ((fun x : TimeVelocity d ↦ scalarSpatialGradient u x j) ∘
      fun y : PDE.Vec d ↦ (z.1, y)) z.2 = _
    rw [fderiv_comp z.2 hgradientDiff
      ((differentiableAt_const (c := z.1)).prodMk differentiableAt_id)]
    congr 1
    exact ((hasFDerivAt_const (x := z.2) z.1).prodMk (hasFDerivAt_id z.2)).fderiv
  have hsucc := coordinateIteratedFDeriv_add_single_at
    (Pi.single (velocityCoord j) 1) (velocityCoord i) u z (by
      simpa [one_add_one_eq_two] using hu)
  change (fderiv ℝ (fun y : PDE.Vec d ↦
      PDE.classicalGradient (fun w : PDE.Vec d ↦ u (z.1, w)) y) z.2
      (PDE.basisVec i)) j = _
  rw [← hgradientApply]
  change (fderiv ℝ (fun y : PDE.Vec d ↦
    scalarSpatialGradient u (z.1, y) j) z.2) (PDE.basisVec i) = _
  rw [hcomp, hgradient.fderiv_eq]
  exact hsucc.symm

end

private theorem coordinateIteratedFDeriv_continuousOn_open
    {d N : ℕ} {Q : Set (TimeVelocity d)} (hQ : IsOpen Q)
    (w : TimeVelocity d → ℝ) (hw : ContDiffOn ℝ N w Q)
    (alpha : TimeVelocityMultiIndex d) (horder : alpha.order ≤ N) :
    ContinuousOn (coordinateIteratedFDeriv alpha w) Q := by
  have hc : ContDiffOn ℝ 0 (coordinateIteratedFDeriv alpha w) Q := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    unfold coordinateIteratedFDeriv
    have hi := (hw.contDiffAt (hQ.mem_nhds hz)).iteratedFDeriv_right
      (m := 0) (i := alpha.coordinateList.length) (by
        simpa using horder)
    exact (contDiffAt_const (c := ContinuousMultilinearMap.apply ℝ _ _
      (fun i ↦ timeVelocityBasis (alpha.coordinateList.get i)))).clm_apply hi
  exact hc.continuousOn

/-- On an open carrier, ambient `C²` regularity within the carrier implies the
scalar anisotropic `C¹,²` regularity used by the parabolic equation. -/
theorem isScalarC12On_of_isOpen_contDiffOn_two
    {d : ℕ} {Q : Set (TimeVelocity d)} {w : TimeVelocity d → ℝ}
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
      (coordinateIteratedFDeriv_continuousOn_open hQ w hw
        (Pi.single (timeCoord d) 1) (by
          simp))
    intro z hz
    exact scalarTimeDerivative_eq_coordinate_open_local w z
      ((hw.contDiffAt (hQ.mem_nhds hz)).of_le (by norm_num))
  · rw [continuousOn_pi]
    intro j
    apply ContinuousOn.congr
      (coordinateIteratedFDeriv_continuousOn_open hQ w hw
        (Pi.single (velocityCoord j) 1) (by
          simp))
    intro z hz
    exact scalarSpatialGradient_eq_coordinate_open_local w z j
      ((hw.contDiffAt (hQ.mem_nhds hz)).of_le (by norm_num))
  · apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    apply ContinuousOn.congr
      (coordinateIteratedFDeriv_continuousOn_open hQ w hw
        (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) (by
          simp))
    intro z hz
    exact scalarSpatialHessian_eq_coordinate_open_local w z i j
      (hw.contDiffAt (hQ.mem_nhds hz))

end
end HypoellipticAleksandrov.Parabolic
