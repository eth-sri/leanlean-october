module

public import RequestProject.LocalConformalGradient


public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LpBoundedMultiplier
public import RequestProject.LocalConformalPullback

/-!
# The physical mass form in given conformal coordinates

The Jacobian square root multiplies the genuine H¹ pullback in disk L².
Change of variables proves its mass norm identity on smooth restrictions;
density and complex polarization prove the full weak mass pairing.
-/

@[expose] public section

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped InnerProductSpace

def localConformalMassDensity (F : PlaneMap) (z : ℂ) : ℂ :=
  (‖fderiv ℝ F z 1‖ : ℝ)

section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R)

section
include R hR F hFs

theorem localConformalMassDensity_continuousOn :
    ContinuousOn (localConformalMassDensity F) closedUnitDisk := Complex.ofRealCLM.continuous.comp_continuousOn
    ((((hFs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).clm_apply
      continuousOn_const).norm).mono (closedBall_subset_ball hR))

theorem exists_localConformalMassDensity_bound :
    ∃ K : ℝ, 0 ≤ K ∧ DiskDerivativeBound F K := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall 0 1).exists_bound_of_continuousOn
    (localConformalMassDensity_continuousOn hR F hFs)
  refine ⟨max B 0, le_max_right _ _, fun z hz => ?_⟩
  have h := hB z (ball_subset_closedBall hz)
  simp_all [localConformalMassDensity]

theorem localConformalMassDensity_aemeasurable :
    AEStronglyMeasurable (localConformalMassDensity F)
      (volume.restrict unitDisk) :=
  ((localConformalMassDensity_continuousOn hR F hFs).mono
    ball_subset_closedBall).aestronglyMeasurable measurableSet_ball

end


theorem localConformalMassDensity_ae_bound F 
    (hK : DiskDerivativeBound F K) :
    ∀ᵐ z ∂volume.restrict unitDisk, ‖localConformalMassDensity F z‖ ≤ K := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  simp_all [localConformalMassDensity]

def localConformalMassPullback {R : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R)
    (hL : IsLipschitzDomain (F '' unitDisk)) {K : ℝ}
    (hK : DiskDerivativeBound F K) :
    NeumannH1 (F '' unitDisk) →L[ℂ] L2 unitDisk :=
  (lpBoundedMultiplier (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)).comp
      ((h1Value unitDisk).comp (localConformalH1Pullback hR F hFs hL))

include R hR F hFs in
theorem localConformalMassPullback_apply
    hL 
    (hK : DiskDerivativeBound F K)
    u :
    localConformalMassPullback hR F hFs hL hK u =
      lpBoundedMultiplier (localConformalMassDensity F)
        (localConformalMassDensity_aemeasurable hR F hFs)
        (localConformalMassDensity_ae_bound F hK)
        (h1Value unitDisk
          (localConformalH1Pullback hR F hFs hL u)) := rfl

end


theorem norm_sq_L2_eq_integral  (v : L2 U) :
    ‖v‖ ^ 2 = ∫ z in U, ‖(v : PlaneMap) z‖ ^ 2 := by
  simpa   using norm_sq_toLp_eq_integral (Lp.memLp v)

private theorem norm_sq_L2_eq_of_ae  (v : L2 U)
    g (h : (v : PlaneMap) =ᵐ[volume.restrict U] g) :
    ‖v‖ ^ 2 = ∫ z in U, ‖g z‖ ^ 2 := (Eq.trans (norm_sq_L2_eq_integral v) (integral_congr_ae (EventuallyEq.fun_comp h fun w => ‖w‖ ^ 2)))

private theorem norm_sq_lpBoundedMultiplier_toLp 
    a (ha : AEStronglyMeasurable a (volume.restrict U))
     (hK : ∀ᵐ z ∂volume.restrict U, ‖a z‖ ≤ K)
    {g : PlaneMap} (hg : MemLp g 2 (volume.restrict U)) :
    ‖lpBoundedMultiplier a ha hK (hg.toLp g)‖ ^ 2 =
      ∫ z in U, ‖a z * g z‖ ^ 2 := by
  apply norm_sq_L2_eq_of_ae
  filter_upwards [lpBoundedMultiplier_ae a ha hK (hg.toLp g),
    hg.coeFn_toLp] with z hmul hval
  rw [hmul, hval]

private theorem localConformalMassDensity_norm_mul
    F  (hF : DifferentiableAt ℂ F z) w :
    ‖localConformalMassDensity F z * w‖ ^ 2 =
      ‖deriv F z‖ ^ 2 * ‖w‖ ^ 2 := by
  have hfd : fderiv ℝ F z 1 = deriv F z := by
    rw [hF.fderiv_restrictScalars ℝ]
    rfl
  rw [norm_mul, mul_pow, localConformalMassDensity,
    Complex.norm_of_nonneg (norm_nonneg _), hfd]

section
variable {R } (hR : 1 < R) (F ) (hFs : RealSmoothOnBall F R) (hb : Bornology.IsBounded (F '' unitDisk)) (hL : IsLipschitzDomain (F '' unitDisk)) (hhol : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk) {C K } (hC : DiskInverseJacobianBound F C) (hK : DiskDerivativeBound F K)

include R hR F hFs hb hL hhol hinj C K hC hK in
theorem localConformalMassPullback_smooth_eq f :
    localConformalMassPullback hR F hFs hL hK
      (smoothTraceH1 (F '' unitDisk) f) =
      lpBoundedMultiplier (localConformalMassDensity F)
        (localConformalMassDensity_aemeasurable hR F hFs)
        (localConformalMassDensity_ae_bound F hK)
        ((smoothTraceTests_memLp unitDisk
          (smoothDiskCompositionLin hR F hFs f)).toLp _) := by
  let M := lpBoundedMultiplier (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)
  calc
    _ = M (h1Value (ball 0 1) (localConformalH1Pullback hR F hFs hL
        (smoothTraceH1 (F '' ball 0 1) f))) :=
      localConformalMassPullback_apply hR F hFs hL hK _
    _ = M (h1Value (ball 0 1) (smoothTraceH1 (ball 0 1)
        (smoothDiskCompositionLin hR F hFs f))) :=
      congrArg (fun v => M (h1Value (ball 0 1) v))
        (localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC f)
    _ = _ := congrArg M (h1Value_smoothTraceH1 (ball 0 1)
      (smoothDiskCompositionLin hR F hFs f))

theorem norm_sq_localConformalMass_smooth_L2  hR F
    (hFs : RealSmoothOnBall F R)
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk) 
    (hK : DiskDerivativeBound F K) f :
    ‖lpBoundedMultiplier (localConformalMassDensity F)
      (localConformalMassDensity_aemeasurable hR F hFs)
      (localConformalMassDensity_ae_bound F hK)
      ((smoothTraceTests_memLp unitDisk
        (smoothDiskCompositionLin hR F hFs f)).toLp _)‖ ^ 2 =
      ∫ z in F '' unitDisk, ‖f z‖ ^ 2 := by
  calc
    _ = ∫ z in ball 0 1,
        ‖localConformalMassDensity F z * smoothDiskCompositionLin hR F hFs f z‖ ^ 2 :=
      norm_sq_lpBoundedMultiplier_toLp (localConformalMassDensity F)
      (localConformalMassDensity_aemeasurable hR F hFs)
      (localConformalMassDensity_ae_bound F hK)
      (smoothTraceTests_memLp (ball 0 1)
        (smoothDiskCompositionLin hR F hFs f))
    _ = ∫ z in ball 0 1, ‖deriv F z‖ ^ 2 * ‖f (F z)‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      change ‖localConformalMassDensity F z * smoothDiskCompositionLin hR F hFs f z‖ ^ 2 =
        ‖deriv F z‖ ^ 2 * ‖f (F z)‖ ^ 2
      rw [smoothDiskCompositionLin_eq_closedDisk hR F hFs f
        (ball_subset_closedBall hz)]
      exact localConformalMassDensity_norm_mul F
        (hhol.differentiableAt (isOpen_ball.mem_nhds hz)) (f (F z))
    _ = ∫ z in F '' ball 0 1, ‖f z‖ ^ 2 :=
      (localConformal_integral_image isOpen_ball hhol hinj (fun z => ‖f z‖ ^ 2)).symm

theorem norm_sq_h1Value_smooth U f :
    ‖h1Value U (smoothTraceH1 U f)‖ ^ 2 = ∫ z in U, ‖f z‖ ^ 2 := by
  rw [h1Value_smoothTraceH1, norm_sq_toLp_eq_integral]

section
include R hR F hFs hb hL hhol hinj C K hC hK

theorem norm_sq_localConformalMassPullback_smooth f :
    ‖localConformalMassPullback hR F hFs hL hK
      (smoothTraceH1 (F '' unitDisk) f)‖ ^ 2 =
      ‖h1Value (F '' unitDisk) (smoothTraceH1 (F '' unitDisk) f)‖ ^ 2 := by
  calc
    _ = ‖lpBoundedMultiplier (localConformalMassDensity F)
        (localConformalMassDensity_aemeasurable hR F hFs)
        (localConformalMassDensity_ae_bound F hK)
        ((smoothTraceTests_memLp (ball 0 1)
          (smoothDiskCompositionLin hR F hFs f)).toLp _)‖ ^ 2 :=
      congrArg (fun v : L2 (ball 0 1) => ‖v‖ ^ 2)
        (localConformalMassPullback_smooth_eq hR F hFs hb hL hhol hinj hC hK f)
    _ = ∫ z in F '' ball 0 1, ‖f z‖ ^ 2 :=
      norm_sq_localConformalMass_smooth_L2 hR F hFs hhol hinj hK f
    _ = _ := (norm_sq_h1Value_smooth _ f).symm

theorem norm_sq_localConformalMassPullback
    u :
    ‖localConformalMassPullback hR F hFs hL hK u‖ ^ 2 =
      ‖h1Value (F '' unitDisk) u‖ ^ 2 := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => ‖localConformalMassPullback hR F hFs hL hK v‖ ^ 2 =
      ‖h1Value (F '' ball 0 1) v‖ ^ 2) u ?_ ?_
  · exact isClosed_eq ((localConformalMassPullback hR F hFs hL hK).continuous.norm.pow 2)
      ((h1Value (F '' ball 0 1)).continuous.norm.pow 2)
  · exact norm_sq_localConformalMassPullback_smooth hR F hFs hb hL hhol hinj hC hK

theorem localConformalMassPullback_inner
    u v :
    ⟪localConformalMassPullback hR F hFs hL hK u,
      localConformalMassPullback hR F hFs hL hK v⟫_ℂ =
      ⟪h1Value (F '' unitDisk) u, h1Value (F '' unitDisk) v⟫_ℂ := common_inner_eq_of_linear_norm_sq
    (localConformalMassPullback hR F hFs hL hK).toLinearMap
    (h1Value (F '' ball 0 1)).toLinearMap
    (norm_sq_localConformalMassPullback hR F hFs hb hL hhol hinj hC hK) u v

end


end


end PolyaNeumann

end
