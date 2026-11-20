module

public import HypoellipticAleksandrov.Parabolic.ScalarCalculus
public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLocalCalculus
import HypoellipticAleksandrov.Parabolic.SmoothScalarWeakDerivativeFamily

/-!
# Ambient `C²` regularity implies scalar parabolic `C¹˒²` regularity
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open scoped Topology

noncomputable section

open TimeVelocityMultiIndex

section
variable {d : ℕ} (u : TimeVelocity d → ℝ) (z : TimeVelocity d)

private theorem coordinateIteratedFDeriv_single_eq (c : TimeVelocityCoord d) (hu : ContDiffAt ℝ 1 u z) :
    coordinateIteratedFDeriv (Pi.single c 1) u z = (fderiv ℝ u z) (timeVelocityBasis c) := by
  have hzero : coordinateIteratedFDeriv 0 u = u := funext (coordinateIteratedFDeriv_zero u)
  simpa only [zero_add, hzero] using
    coordinateIteratedFDeriv_add_single_at 0 c u z (by
      simpa [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.velocity,
        TimeVelocityMultiIndex.timeOrder, VelocityMultiIndex.order] using hu)

private theorem scalarTimeDerivative_eq_coordinate_local
    (hu : ContDiffAt ℝ 1 u z) :
    scalarTimeDerivative u z =
      coordinateIteratedFDeriv (Pi.single (timeCoord d) 1) u z := by
  rw [coordinateIteratedFDeriv_single_eq u z _ hu, timeVelocityBasis_time]
  unfold scalarTimeDerivative
  have hsF := (hu.differentiableAt (by norm_num)).hasFDerivAt.comp z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  have hs : HasDerivAt (fun r : ℝ ↦ u (r, z.2))
      ((fderiv ℝ u z) (1, 0)) z.1 := by
    convert hsF.hasDerivAt using 1
    all_goals simp [Function.comp_def]
  exact hs.deriv

private theorem scalarSpatialGradient_eq_coordinate_local (j : Fin d)
    (hu : ContDiffAt ℝ 1 u z) :
    scalarSpatialGradient u z j =
      coordinateIteratedFDeriv (Pi.single (velocityCoord j) 1) u z := by
  rw [coordinateIteratedFDeriv_single_eq u z _ hu, timeVelocityBasis_velocity,
    scalarSpatialGradient, PDE.classicalGradient_apply]
  have hs : HasFDerivAt (fun y : PDE.Vec d ↦ u (z.1, y))
      ((fderiv ℝ u z).comp (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d))) z.2 :=
    (hu.differentiableAt (by norm_num)).hasFDerivAt.comp z.2
      ((hasFDerivAt_const (x := z.2) z.1).prodMk (hasFDerivAt_id z.2))
  rw [hs.fderiv]
  simp

private theorem scalarSpatialHessian_eq_coordinate_local (i j : Fin d)
    (hu : ContDiffAt ℝ 2 u z) :
    scalarSpatialHessian u z i j =
      coordinateIteratedFDeriv
        (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) u z := by
  classical
  let q : TimeVelocity d → ℝ :=
    coordinateIteratedFDeriv (Pi.single (velocityCoord j) 1) u
  have hq : ContDiffAt ℝ 1 q z := by
    have hr : ContDiffAt ℝ 1
        (fun x ↦ (fderiv ℝ u x) (timeVelocityBasis (velocityCoord j))) z :=
      (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    apply hr.congr_of_eventuallyEq
    filter_upwards [hu.eventually (by simp)] with x hx
    exact coordinateIteratedFDeriv_single_eq u x _ (hx.of_le (by norm_num))
  have hgradient : (fun x : TimeVelocity d ↦ scalarSpatialGradient u x j) =ᶠ[nhds z] q := by
    filter_upwards [hu.eventually (by simp)] with x hx
    exact scalarSpatialGradient_eq_coordinate_local u x j (hx.of_le (by norm_num))
  have hgradientDiff : DifferentiableAt ℝ
      (fun x : TimeVelocity d ↦ scalarSpatialGradient u x j) z :=
    hgradient.differentiableAt_iff.mpr (hq.differentiableAt (by norm_num))
  have hslice : ContDiffAt ℝ 2 (fun y : PDE.Vec d ↦ u (z.1, y)) z.2 :=
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
      have hd : DifferentiableAt ℝ
          (fderiv ℝ (fun w : PDE.Vec d ↦ u (z.1, w))) z.2 :=
        (hslice.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
      exact hd.clm_apply (differentiableAt_const (c := PDE.basisVec k))
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
    (Pi.single (velocityCoord j) 1) (velocityCoord i) u z (by convert hu using 1 <;> norm_num)
  change (fderiv ℝ (fun y : PDE.Vec d ↦
      PDE.classicalGradient (fun w : PDE.Vec d ↦ u (z.1, w)) y) z.2
      (PDE.basisVec i)) j = _
  rw [← hgradientApply]
  change (fderiv ℝ (fun y : PDE.Vec d ↦
    scalarSpatialGradient u (z.1, y) j) z.2) (PDE.basisVec i) = _
  rw [hcomp, hgradient.fderiv_eq]
  simpa [q] using hsucc.symm

end

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
      (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_continuousOn hQ w hw
        (Pi.single (timeCoord d) 1) (by simp))
    intro z hz
    exact scalarTimeDerivative_eq_coordinate_local w z
      ((hw.contDiffAt (hQ.mem_nhds hz)).of_le (by norm_num))
  · rw [continuousOn_pi]
    intro j
    apply ContinuousOn.congr
      (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_continuousOn hQ w hw
        (Pi.single (velocityCoord j) 1) (by simp))
    intro z hz
    exact scalarSpatialGradient_eq_coordinate_local w z j
      ((hw.contDiffAt (hQ.mem_nhds hz)).of_le (by norm_num))
  · apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    apply ContinuousOn.congr
      (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_continuousOn hQ w hw
        (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) (by simp))
    intro z hz
    exact scalarSpatialHessian_eq_coordinate_local w z i j
      (hw.contDiffAt (hQ.mem_nhds hz))

section
variable {d : ℕ} {v : TimeVelocity d → ℝ} (hv : ContDiff ℝ 2 v)
include hv

/-- Globally `C²` functions are anisotropically `C¹,²` on every set. -/
theorem isScalarC12On_of_contDiff_two (Q : Set (TimeVelocity d)) : IsScalarC12On v Q :=
  (isScalarC12On_of_isOpen_contDiffOn_two isOpen_univ hv.contDiffOn).mono (Set.subset_univ Q)

section
variable (z : TimeVelocity d)

/-- The scalar time derivative is the canonical time-coordinate derivative. -/
theorem scalarTimeDerivative_eq_coordinateIteratedFDeriv_of_contDiff_two :
    scalarTimeDerivative v z =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (timeCoord d) 1) v z :=
  scalarTimeDerivative_eq_coordinate_local v z ((hv.of_le (by norm_num)).contDiffAt)

/-- Each scalar spatial-gradient entry is its canonical velocity-coordinate
derivative. -/
theorem scalarSpatialGradient_apply_eq_coordinateIteratedFDeriv_of_contDiff_two (j : Fin d) :
    scalarSpatialGradient v z j =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (velocityCoord j) 1) v z :=
  scalarSpatialGradient_eq_coordinate_local v z j ((hv.of_le (by norm_num)).contDiffAt)

/-- The ordered Hessian entry `(i,j)` is `D_i(D_j v)`. -/
theorem scalarSpatialHessian_apply_eq_coordinateIteratedFDeriv_of_contDiff_two (i j : Fin d) :
    scalarSpatialHessian v z i j =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (velocityCoord j) 1 +
          Pi.single (velocityCoord i) 1) v z :=
  scalarSpatialHessian_eq_coordinate_local v z i j hv.contDiffAt

end

end

end

end HypoellipticAleksandrov.Parabolic
