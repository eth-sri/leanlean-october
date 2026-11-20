module

public import RequestProject.DiskCoordinates

public import RequestProject.LpBoundedMultiplier
public import RequestProject.LocalConformalPullback
public import RequestProject.LocalConformalGradient
public import RequestProject.PlanarNotation

/-!
# The physical mass form in given conformal coordinates

The Jacobian square root multiplies the genuine H¹ pullback in disk L².
Change of variables proves its mass norm identity on smooth restrictions;
density and complex polarization prove the full weak mass pairing.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped InnerProductSpace

section

variable (F : ℂ → ℂ) (Φ : SmoothDiskMap) (hL : IsLipschitzDomain Φ.domain)

include F in
def localConformalMassDensity (z : ℂ) : ℂ :=
  (‖fderiv ℝ F z 1‖ : ℝ)

theorem localConformalMassDensity_continuousOn :
    ContinuousOn (localConformalMassDensity Φ.map) closedDisk := Complex.ofRealCLM.continuous.comp_continuousOn
    ((((Φ.smooth.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).clm_apply
      continuousOn_const).norm).mono (closedBall_subset_ball Φ.one_lt_radius))

theorem exists_localConformalMassDensity_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ unitDisk, ‖fderiv ℝ Φ.map z 1‖ ≤ K := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall 0 1).exists_bound_of_continuousOn
    (localConformalMassDensity_continuousOn Φ)
  refine ⟨max B 0, le_max_right _ _, fun z hz => ?_⟩
  
  simpa [localConformalMassDensity] using (hB z (ball_subset_closedBall hz)).trans (le_max_left B 0)

theorem localConformalMassDensity_aemeasurable :
    AEStronglyMeasurable (localConformalMassDensity Φ.map)
      (volume.restrict unitDisk) :=
  ((localConformalMassDensity_continuousOn Φ).mono
    ball_subset_closedBall).aestronglyMeasurable measurableSet_ball

theorem localConformalMassDensity_ae_bound {K : ℝ}
    (hK : ∀ z ∈ unitDisk, ‖fderiv ℝ F z 1‖ ≤ K) :
    ∀ᵐ z ∂volume.restrict unitDisk, ‖localConformalMassDensity F z‖ ≤ K := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  simpa [localConformalMassDensity] using hK z hz

include hL in
def SmoothDiskMap.massPullback {K : ℝ} (hK : ∀ z ∈ unitDisk, ‖fderiv ℝ Φ.map z 1‖ ≤ K) :
    NeumannH1 Φ.domain →L[ℂ] L2 unitDisk :=
  (lpBoundedMultiplier (localConformalMassDensity Φ.map)
    (localConformalMassDensity_aemeasurable Φ)
    (localConformalMassDensity_ae_bound Φ.map hK)).comp
      ((h1Value unitDisk).comp (Φ.h1Pullback hL))

theorem localConformalMassPullback_apply {K : ℝ} (hK : ∀ z ∈ unitDisk, ‖fderiv ℝ Φ.map z 1‖ ≤ K)
    (u : NeumannH1 Φ.domain) :
    Φ.massPullback hL hK u =
      lpBoundedMultiplier (localConformalMassDensity Φ.map)
        (localConformalMassDensity_aemeasurable Φ)
        (localConformalMassDensity_ae_bound Φ.map hK)
        (h1Value unitDisk
          (Φ.h1Pullback hL u)) := rfl

private theorem norm_sq_L2_eq_of_ae {U : Set ℂ} (v : L2 U)
    (g : ℂ → ℂ) (h : (v : ℂ → ℂ) =ᵐ[volume.restrict U] g) :
    ‖v‖ ^ 2 = ∫ z in U, ‖g z‖ ^ 2 := (integral_norm_sq_lp v).symm.trans
    (integral_congr_ae (h.fun_comp (fun w : ℂ => ‖w‖ ^ 2)))

private theorem norm_sq_lpBoundedMultiplier_toLp {U : Set ℂ}
    (a : ℂ → ℂ) (ha : AEStronglyMeasurable a (volume.restrict U))
    {K : ℝ} (hK : ∀ᵐ z ∂volume.restrict U, ‖a z‖ ≤ K)
    {g : ℂ → ℂ} (hg : MemLp g 2 (volume.restrict U)) :
    ‖lpBoundedMultiplier a ha hK (hg.toLp g)‖ ^ 2 =
      ∫ z in U, ‖a z * g z‖ ^ 2 := by
  apply norm_sq_L2_eq_of_ae
  filter_upwards [lpBoundedMultiplier_ae a ha hK (hg.toLp g),
    hg.coeFn_toLp] with z hmul hval
  simp [*]

private theorem localConformalMassDensity_norm_mul {z : ℂ} (hF : DifferentiableAt ℂ F z) (w : ℂ) :
    ‖localConformalMassDensity F z * w‖ ^ 2 =
      ‖deriv F z‖ ^ 2 * ‖w‖ ^ 2 := by
  have hfd : fderiv ℝ F z 1 = deriv F z := by
    rw [hF.fderiv_restrictScalars ℝ]
    rfl
  simp [mul_pow, localConformalMassDensity, hfd]

end

section

variable (Φ : ControlledDiskMap) (U : Set ℂ) (u : NeumannH1 Φ.domain) (f : smoothTraceTests)

theorem localConformalMassPullback_smooth_eq :
    Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper
      (smoothTraceH1 Φ.domain f) =
      lpBoundedMultiplier (localConformalMassDensity Φ.map)
        (localConformalMassDensity_aemeasurable Φ)
        (localConformalMassDensity_ae_bound Φ.map Φ.deriv_upper)
        ((smoothTraceTests_memLp unitDisk
          (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f)).toLp _) := by
  let M := lpBoundedMultiplier (localConformalMassDensity Φ.map)
    (localConformalMassDensity_aemeasurable Φ)
    (localConformalMassDensity_ae_bound Φ.map Φ.deriv_upper)
  calc
    _ = _ :=
      localConformalMassPullback_apply Φ Φ.lipschitzDomain Φ.deriv_upper _
    _ = _ :=
      congrArg (fun v => M (h1Value unitDisk v))
        (localConformalH1Pullback_smooth Φ f)
    _ = _ := congrArg M (h1Value_smoothTraceH1 unitDisk
      _)

theorem norm_sq_localConformalMass_smooth_L2 (Φ : SmoothDiskMap)
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (hinj : InjOn Φ.map unitDisk) {K : ℝ}
    (hK : ∀ z ∈ unitDisk, ‖fderiv ℝ Φ.map z 1‖ ≤ K) (f : smoothTraceTests) :
    ‖lpBoundedMultiplier (localConformalMassDensity Φ.map)
      (localConformalMassDensity_aemeasurable Φ)
      (localConformalMassDensity_ae_bound Φ.map hK)
      ((smoothTraceTests_memLp unitDisk
        (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f)).toLp _)‖ ^ 2 =
      ∫ z in Φ.domain, ‖f z‖ ^ 2 := by
  calc
    _ = _ :=
      norm_sq_lpBoundedMultiplier_toLp (localConformalMassDensity Φ.map)
      (localConformalMassDensity_aemeasurable Φ)
      _
      _
    _ = ∫ z in unitDisk, ‖deriv Φ.map z‖ ^ 2 * ‖f _‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      change ‖localConformalMassDensity Φ.map z * smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f z‖ ^ 2 =
        _
      rw [smoothDiskCompositionLin_eq_closedDisk Φ.one_lt_radius Φ.map Φ.smooth f
        (ball_subset_closedBall hz)]
      exact localConformalMassDensity_norm_mul Φ.map
        (hhol.differentiableAt (isOpen_ball.mem_nhds hz)) _
    _ = _ :=
      (localConformal_integral_image isOpen_ball hhol hinj (fun z => ‖f z‖ ^ 2)).symm

theorem norm_sq_h1Value_smooth :
    ‖h1Value U (smoothTraceH1 U f)‖ ^ 2 = ∫ z in U, ‖f z‖ ^ 2 := by
  rw [h1Value_smoothTraceH1, norm_sq_toLp_eq_integral]

theorem norm_sq_localConformalMassPullback_smooth :
    ‖Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper
      (smoothTraceH1 Φ.domain f)‖ ^ 2 =
      ‖h1Value Φ.domain (smoothTraceH1 Φ.domain f)‖ ^ 2 := calc
    _ = _ :=
      congrArg (fun v : L2 unitDisk => ‖v‖ ^ 2)
        (localConformalMassPullback_smooth_eq Φ f)
    _ = _ :=
      norm_sq_localConformalMass_smooth_L2 Φ Φ.holomorphic Φ.inj Φ.deriv_upper f
    _ = _ := (norm_sq_h1Value_smooth _ f).symm

theorem norm_sq_localConformalMassPullback :
    ‖Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper u‖ ^ 2 =
      ‖h1Value Φ.domain u‖ ^ 2 := by
  refine (denseRange_smoothTraceH1Lin Φ.bounded Φ.lipschitzDomain).induction_on
     u ?_ ?_
  · exact isClosed_eq ((Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper).continuous.norm.pow 2)
      ((h1Value Φ.domain).continuous.norm.pow 2)
  · exact norm_sq_localConformalMassPullback_smooth Φ

theorem localConformalMassPullback_inner (v : NeumannH1 Φ.domain) :
    ⟪Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper u,
      Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper v⟫_ℂ =
      ⟪h1Value Φ.domain u, h1Value Φ.domain v⟫_ℂ := inner_eq_of_linear_norm_sq
    (Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper).toLinearMap
    (h1Value Φ.domain).toLinearMap
    (norm_sq_localConformalMassPullback Φ) u v

end

end PolyaNeumann

end
