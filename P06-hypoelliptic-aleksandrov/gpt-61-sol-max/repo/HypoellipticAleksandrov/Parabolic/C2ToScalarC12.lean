module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLocalCalculus

/-!
# Ambient `C²` regularity implies scalar parabolic `C¹˒²` regularity
-/

 public section

namespace HypoellipticAleksandrov.Parabolic



section

open TimeVelocityMultiIndex

variable {d : ℕ} (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d)

private theorem scalarTimeDerivative_eq_coordinate_local

    (hu : ContDiffAt ℝ 1 u z) :
    scalarTimeDerivative u z =
      coordinateIteratedFDeriv (Pi.single (timeCoord d) 1) u z := by
  have h := coordinateIteratedFDeriv_add_single_at
    (0 : TimeVelocityMultiIndex d) (timeCoord d) u z
      (by simp_all [TimeVelocityMultiIndex.order, VelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity])
  simp only [zero_add, timeVelocityBasis_time] at h
  rw [show coordinateIteratedFDeriv (0 : TimeVelocityMultiIndex d) u = u by
    funext x; exact coordinateIteratedFDeriv_zero u x] at h
  rw [h]
  unfold scalarTimeDerivative
  have hsF := (hu.differentiableAt (by norm_num)).hasFDerivAt.comp z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))

  exact (show HasDerivAt (fun r  ↦ u (r, z.2))
      ((fderiv ℝ u z) (1, 0)) z.1 by
      convert hsF.hasDerivAt using 1
      all_goals simp [Function.comp_def]).deriv

private theorem scalarSpatialGradient_eq_coordinate_local
     (j : Fin d)
    (hu : ContDiffAt ℝ 1 u z) :
    scalarSpatialGradient u z j =
      coordinateIteratedFDeriv (Pi.single (velocityCoord j) 1) u z := by
  have h := coordinateIteratedFDeriv_add_single_at
    (0 : TimeVelocityMultiIndex d) (velocityCoord j) u z
      (by simp_all [TimeVelocityMultiIndex.order, VelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity])
  simp only [zero_add, timeVelocityBasis_velocity] at h
  rw [show coordinateIteratedFDeriv (0 : TimeVelocityMultiIndex d) u = u by
    funext x; exact coordinateIteratedFDeriv_zero u x] at h
  rw [h, scalarSpatialGradient, PDE.classicalGradient_apply]
  have hs : HasFDerivAt (fun y  ↦ u (z.1, y))
      ((fderiv ℝ u z).comp (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d))) z.2 :=
    (hu.differentiableAt (by norm_num)).hasFDerivAt.comp z.2
      ((hasFDerivAt_const (x := z.2) z.1).prodMk (hasFDerivAt_id z.2))
  rw [hs.fderiv]
  simp

private theorem scalarSpatialHessian_eq_coordinate_local
     (i j : Fin d)
    (hu : ContDiffAt ℝ 2 u z) :
    scalarSpatialHessian u z i j =
      coordinateIteratedFDeriv
        (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) u z := by
  let sharedTerm_172f2ac7e0 := ((fun w : PDE.Vec d ↦ u (z.1, w)))
  let sharedTerm_65981b94d2 := ((fun x : TimeVelocity d ↦ scalarSpatialGradient u x j))
  let sharedTerm_9064faf8ae := ((fderiv ℝ (fun y : PDE.Vec d ↦ scalarSpatialGradient u (z.1, y) j) z.2))
  classical
  let q  :=
    coordinateIteratedFDeriv (Pi.single (velocityCoord j) 1) u

  have hgradient : sharedTerm_65981b94d2 =ᶠ[nhds z] q := by
    filter_upwards [hu.eventually (by simp)] with x hx
    exact scalarSpatialGradient_eq_coordinate_local u x j (hx.of_le (by norm_num))


  have hgradientApply :
      (fderiv ℝ (fun y  ↦
          PDE.classicalGradient sharedTerm_172f2ac7e0 y j) z.2)
          (PDE.basisVec i) =
        (fderiv ℝ (fun y  ↦
          PDE.classicalGradient sharedTerm_172f2ac7e0 y) z.2
          (PDE.basisVec i)) j := by

    rw [fderiv_pi (((differentiableAt_pi.mp (by
        apply differentiableAt_pi.2
        intro k

        exact (((hu.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply (differentiableAt_const (c := PDE.basisVec k))))))]
    simp
  have hcomp :
      sharedTerm_9064faf8ae =
        (fderiv ℝ sharedTerm_65981b94d2 z).comp
          (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d)) := by
    change fderiv ℝ (sharedTerm_65981b94d2 ∘
      fun y  ↦ (z.1, y)) z.2 = _
    rw [fderiv_comp z.2 (hgradient.differentiableAt_iff.mpr ((show ContDiffAt ℝ 1 q z by

        apply ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).congr_of_eventuallyEq
        filter_upwards [hu.eventually (by simp)] with x hx
        have hadd := coordinateIteratedFDeriv_add_single_at
          (0 : TimeVelocityMultiIndex d) (velocityCoord j) u x
          (by simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
            TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity] using
            hx.of_le (by norm_num))
        rw [show coordinateIteratedFDeriv (0 : TimeVelocityMultiIndex d) u = u by
          funext y; exact coordinateIteratedFDeriv_zero u y] at hadd
        simpa [q] using hadd).differentiableAt (by norm_num)))
      ((differentiableAt_const (c := z.1)).prodMk differentiableAt_id)]
    congr 1
    exact ((hasFDerivAt_const (x := z.2) z.1).prodMk (hasFDerivAt_id z.2)).fderiv
  have hsucc := coordinateIteratedFDeriv_add_single_at
    (Pi.single (velocityCoord j) 1) (velocityCoord i) u z (by
      simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
        TimeVelocityMultiIndex.velocity, TimeVelocityMultiIndex.timeOrder,
        timeCoord, velocityCoord, Pi.single_apply,
        show (1 : WithTop ℕ∞) + 1 = 2 by rfl] using hu)
  change (fderiv ℝ (fun y  ↦
      PDE.classicalGradient sharedTerm_172f2ac7e0 y) z.2
      (PDE.basisVec i)) j = _
  rw [← hgradientApply]
  change sharedTerm_9064faf8ae (PDE.basisVec i) = _
  rw [hcomp, hgradient.fderiv_eq]
  simpa [q] using hsucc.symm

private theorem coordinateIteratedFDeriv_contDiff_local
    {d m : ℕ} (alpha : TimeVelocityMultiIndex d)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : ContDiff ℝ (m + alpha.order) f) :
    ContDiff ℝ m (coordinateIteratedFDeriv alpha f) := by
  unfold coordinateIteratedFDeriv
  have hi := hf.iteratedFDeriv_right
    (m := m) (i := alpha.coordinateList.length) (by simp)
  exact (contDiff_const (c := ContinuousMultilinearMap.apply ℝ _ _
    (fun i ↦ timeVelocityBasis (alpha.coordinateList.get i)))).clm_apply hi

variable {d : ℕ} {v : HypoellipticAleksandrov.Parabolic.ScalarField d} (hv : ContDiff ℝ 2 v)

include hv in
/-- An ambient `C²` function has the scalar anisotropic `C¹˒²` regularity
required on every carrier. -/
theorem isScalarC12On_of_contDiff_two
     (D : HypoellipticAleksandrov.Parabolic.Region d) :
    IsScalarC12On v D := by
  refine ⟨hv.continuous.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ((hv.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).differentiableAt
  · intro z hz
    exact hv.contDiffAt.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)
  · apply Continuous.continuousOn
    apply Continuous.congr (coordinateIteratedFDeriv_contDiff_local
      (Pi.single (timeCoord d) 1) v (by norm_num at *; exact hv)).continuous
    intro z
    exact (scalarTimeDerivative_eq_coordinate_local v z
      ((hv.of_le (by norm_num)).contDiffAt)).symm
  · apply Continuous.continuousOn
    apply continuous_pi
    intro j
    apply Continuous.congr (coordinateIteratedFDeriv_contDiff_local
      (Pi.single (velocityCoord j) 1) v (by norm_num at *; exact hv)).continuous
    intro z
    exact (scalarSpatialGradient_eq_coordinate_local v z j
      ((hv.of_le (by norm_num)).contDiffAt)).symm
  · apply Continuous.continuousOn
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    apply Continuous.congr (coordinateIteratedFDeriv_contDiff_local
      (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) v
      (by norm_num at *; exact hv)).continuous
    intro z
    exact (scalarSpatialHessian_eq_coordinate_local v z i j hv.contDiffAt).symm

variable (z : TimeVelocity d)

include hv
/-- The scalar time derivative is the canonical time-coordinate derivative. -/
theorem scalarTimeDerivative_eq_coordinateIteratedFDeriv_of_contDiff_two

     :
    scalarTimeDerivative v z =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (timeCoord d) 1) v z :=
  scalarTimeDerivative_eq_coordinate_local v z ((hv.of_le (by norm_num)).contDiffAt)

/-- Each scalar spatial-gradient entry is its canonical velocity-coordinate
derivative. -/
theorem scalarSpatialGradient_apply_eq_coordinateIteratedFDeriv_of_contDiff_two

     (j : Fin d) :
    scalarSpatialGradient v z j =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (velocityCoord j) 1) v z :=
  scalarSpatialGradient_eq_coordinate_local v z j ((hv.of_le (by norm_num)).contDiffAt)

/-- The ordered Hessian entry `(i,j)` is `D_i(D_j v)`. -/
theorem scalarSpatialHessian_apply_eq_coordinateIteratedFDeriv_of_contDiff_two

     (i j : Fin d) :
    scalarSpatialHessian v z i j =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (velocityCoord j) 1 +
          Pi.single (velocityCoord i) 1) v z :=
  scalarSpatialHessian_eq_coordinate_local v z i j hv.contDiffAt

end

end HypoellipticAleksandrov.Parabolic
