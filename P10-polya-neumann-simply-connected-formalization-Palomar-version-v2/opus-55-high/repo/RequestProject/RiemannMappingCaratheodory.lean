module

public import RequestProject.RiemannMappingCapWinding
public import Mathlib.Topology.ExtendFrom
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The actual continuous closed-disk Riemann-map extension

The full interior-approach limits proved from finite energy and actual
Jordan-boundary winding are assembled with `extendFrom`. The extension
agrees with the original holomorphic map on the open disk, has compact
image equal to the physical closure, and maps the unit circle onto the
physical frontier. Boundary injectivity is not assumed in these results.
It is then proved from genuine connected fibers and circle-patch Cauchy
continuation, yielding the closed-disk homeomorphism.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter MeasureTheory Complex
open scoped Topology ComplexConjugate

/-- The actual full-approach extension of the interior conformal map.
Its continuity on the closed disk is proved below from the physical
domain hypotheses. Values outside the closed disk are immaterial. -/
def riemannMappingClosedExtension (F : ℂ → ℂ) : ℂ → ℂ :=
  extendFrom (ball (0 : ℂ) 1) F

variable (F : ℂ → ℂ) {Ω : Set ℂ} (G : ℂ → ℂ)

/-- The true extension retains every value of the supplied interior map. -/
theorem riemannMappingClosedExtension_eqOn (hF : DifferentiableOn ℂ F (ball 0 1)) :
    EqOn (riemannMappingClosedExtension F) F (ball 0 1) := by
  intro z hz
  exact extendFrom_extends hF.continuousOn z hz

/-- The full boundary limit supplies convergence at every closed-disk
point; interior points use the actual holomorphic map's continuity. -/
theorem riemannMapping_exists_limit_closedDisk
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    {z : ℂ} (hz : z ∈ closedBall 0 1) :
    ∃ p : ℂ, Tendsto F (𝓝[ball 0 1] z) (𝓝 p) := by
  have hn  := mem_closedBall_zero_iff.mp hz
  rcases eq_or_lt_of_le hn with hn | hn
  · obtain ⟨p, hp, _⟩ := riemannMapping_exists_unique_boundary_limit hb hL hsc F hF hinj himage hn
    grind
  · exact ⟨F z, hF.continuousOn z (mem_ball_zero_iff.mpr hn)⟩

/-- The actual closed-disk extension is continuous at boundary points
with respect to all closed-disk approaches, not only interior rays. -/
theorem riemannMappingClosedExtension_continuousOn
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω) :
    ContinuousOn (riemannMappingClosedExtension F) (closedBall 0 1) := by
  apply continuousOn_extendFrom
  · rw [closure_ball 0 one_ne_zero]
  · intro z hz
    exact riemannMapping_exists_limit_closedDisk hb hL hsc F hF hinj himage hz

/-- Every actual boundary value is in the physical frontier. This
uses the previously constructed full limit, including its interior
inverse exclusion of an interior image limit. -/
theorem riemannMappingClosedExtension_mem_frontier
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) : riemannMappingClosedExtension F ζ ∈ frontier Ω := by
  obtain ⟨p, hp, _⟩ := riemannMapping_exists_unique_boundary_limit hb hL hsc F hF hinj himage hζ
  have he : riemannMappingClosedExtension F ζ = p := extendFrom_eq (by
    rw [closure_ball 0 one_ne_zero, mem_closedBall_zero_iff, hζ]) hp.2
  simp_all

/-- The extension has exactly the original open-disk physical image. -/
theorem riemannMappingClosedExtension_open_image (hF : DifferentiableOn ℂ F (ball 0 1)) :
    riemannMappingClosedExtension F '' ball 0 1 = F '' ball 0 1 :=
  (riemannMappingClosedExtension_eqOn F hF).image_eq

private theorem closedDisk_image_eq_closure_of_continuousOn (hG : ContinuousOn G (closedBall (0 : ℂ) 1)) :
    G '' closedBall (0 : ℂ) 1 = closure (G '' ball (0 : ℂ) 1) := by
  have hcl : closure (ball (0 : ℂ) 1) = closedBall (0 : ℂ) 1 :=
    closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)
  have hGc : ContinuousOn G (closure (ball (0 : ℂ) 1)) := by
    simp_all
  apply Subset.antisymm
  · simpa only [hcl] using hGc.image_closure
  · apply closure_minimal
    · rintro w ⟨z, hz, rfl⟩
      exact ⟨z, ball_subset_closedBall hz, rfl⟩
    · exact ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hG).isClosed

/-- The compact closed-disk image is exactly the closure of the actual
physical domain, obtained without boundary injectivity. -/
theorem riemannMappingClosedExtension_closed_image
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω) :
    riemannMappingClosedExtension F '' closedBall 0 1 = closure Ω := by
  simp [closedDisk_image_eq_closure_of_continuousOn _     (riemannMappingClosedExtension_continuousOn hb hL hsc F hF hinj himage), riemannMappingClosedExtension_open_image F hF, himage]

/-- The extension maps the actual unit circle onto the entire physical
frontier. Surjectivity follows from the compact image identity; an
interior source point cannot map to a frontier point. -/
theorem riemannMappingClosedExtension_sphere_image
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω) :
    riemannMappingClosedExtension F '' sphere 0 1 = frontier Ω := by
  apply Subset.antisymm
  · rintro w ⟨ζ, hζ, rfl⟩
    exact riemannMappingClosedExtension_mem_frontier hb hL hsc F hF hinj himage
      (by simp_all)
  · intro w hw
    have hwcl := frontier_subset_closure hw
    rw [← riemannMappingClosedExtension_closed_image hb hL hsc F hF hinj himage] at hwcl
    obtain ⟨z, hz, he⟩ := hwcl
    refine ⟨z, ?_, he⟩
    have hn  := mem_closedBall_zero_iff.mp hz
    rcases eq_or_lt_of_le hn with hn | hn
    · simp_all
    · have hzD  := mem_ball_zero_iff.mpr hn
      have hwΩ : w ∈ Ω := by
        rw [← himage]
        exact ⟨z, hzD, (riemannMappingClosedExtension_eqOn F hF hzD).symm.trans he⟩
      simp_all [hL.1.1.frontier_eq]

/-- On the closed disk the actual interior image points have exactly
the original interior source points as preimages. -/
theorem riemannMappingClosedExtension_mem_domain_iff
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    {z : ℂ} (hz : z ∈ closedBall 0 1) :
    riemannMappingClosedExtension F z ∈ Ω ↔ z ∈ ball 0 1 := by
  constructor
  · have hn  := mem_closedBall_zero_iff.mp hz
    rcases eq_or_lt_of_le hn with hn | hn
    · have hfront := riemannMappingClosedExtension_mem_frontier hb hL hsc F hF hinj himage hn
      simp_all [hL.1.1.frontier_eq]
    simp_all
  · intro hzD
    rw [riemannMappingClosedExtension_eqOn F hF hzD]
    grind

/-- The extension is injective whenever one of its source points is
interior. The only remaining injectivity question concerns two distinct
points of the unit circle. -/
theorem riemannMappingClosedExtension_eq_of_eq_of_mem_disk
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    {z w : ℂ} (hz : z ∈ ball 0 1) (hw : w ∈ closedBall 0 1)
    (he : riemannMappingClosedExtension F z = riemannMappingClosedExtension F w) : z = w := by
  have hwD  :=
    (riemannMappingClosedExtension_mem_domain_iff hb hL hsc F hF hinj himage hw).mp (he ▸ (riemannMappingClosedExtension_mem_domain_iff hb hL hsc F hF hinj himage
      (ball_subset_closedBall hz)).mpr hz)
  exact hinj hz hwD (by
    simp_all [riemannMappingClosedExtension_eqOn F hF hz, riemannMappingClosedExtension_eqOn F hF hwD])

/-- A physical frontier fiber of the actual continuous extension is
connected. Compactness selects a physical chart whose entire interior
inverse image lies in any prescribed neighborhood of the fiber; the
true connected graph region cannot split between disjoint neighborhoods.
No monotonicity or connected-fiber premise is assumed. -/
theorem riemannMappingClosedExtension_boundary_fiber_connected
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    IsConnected (closedBall 0 1 ∩ riemannMappingClosedExtension F ⁻¹' {p}) := by
  let G := riemannMappingClosedExtension F
  let A := closedBall 0 1 ∩ G ⁻¹' {p}
  have hGc  :=
    riemannMappingClosedExtension_continuousOn hb hL hsc F hF hinj himage
  have hEq  := riemannMappingClosedExtension_eqOn F hF
  have hAc : IsClosed A := hGc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hAk  :=
    (isCompact_closedBall 0 1).of_isClosed_subset hAc inter_subset_left
  refine ⟨by
    have hpim : p ∈ G '' sphere 0 1 := by
      rwa [riemannMappingClosedExtension_sphere_image hb hL hsc F hF hinj himage]
    obtain ⟨ζ, hζ, he⟩ := hpim
    exact ⟨ζ, sphere_subset_closedBall hζ, he⟩, ?_⟩
  apply isPreconnected_iff_subset_of_disjoint_closed.mpr
  intro u v hu hv hAuv hAdisj
  obtain ⟨U, V, hUo, hVo, hKuU, hKvV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hAk.inter_right hu) (hAk.inter_right hv) (by
    apply Set.disjoint_left.mpr
    intro z hzu hzv
    have hz : z ∈ A ∩ (u ∩ v) := ⟨hzu.1, hzu.2, hzv.2⟩
    grind)
  have hAUV : A ⊆ U ∪ V := by
    grind
  obtain ⟨d, hd, hdball⟩ := Metric.isOpen_iff.mp (((isCompact_closedBall 0 1).diff (hUo.union hVo)).image_of_continuousOn (hGc.mono diff_subset)).isClosed.isOpen_compl p (by
    grind)
  obtain ⟨c, r, h, KC, f, hch, hBball⟩ := exists_small_chart hL hp hd
  let B := chartBox p c r h
  obtain ⟨J, hJ, hJm, hJF, hFJ⟩ := RiemannInterior.exists_holomorphic_inverse isOpen_ball
    (convex_ball 0 1).isPreconnected hF hinj
  rw [himage] at hJ hJm hFJ
  let S := J '' (Ω ∩ B)
  have hSclosedDisk : S ⊆ closedBall 0 1 := by
    rintro z ⟨w, hw, rfl⟩
    exact ball_subset_closedBall (hJm hw.1)
  have hAcl : A ⊆ closure S := by
    intro ζ hζ
    have hζcl : ζ ∈ closure (ball 0 1) := by
      rw [closure_ball 0 one_ne_zero]
      grind
    letI  := mem_closure_iff_nhdsWithin_neBot.mp hζcl
    have hlim : Tendsto F (𝓝[ball 0 1] ζ) (𝓝 p) := by
      have ht := tendsto_extendFrom (riemannMapping_exists_limit_closedDisk hb hL hsc F hF hinj
        himage hζ.1)
      change Tendsto F (𝓝[ball 0 1] ζ) (𝓝 (G ζ)) at ht
      grind
    exact mem_closure_of_tendsto
      (tendsto_id.mono_left nhdsWithin_le_nhds) (by
      filter_upwards [self_mem_nhdsWithin, hlim.eventually ((isOpen_chartBox p c r h).mem_nhds hch.center_mem_box)] with z hz hzB
      exact ⟨F z, ⟨himage ▸ mem_image_of_mem F hz, hzB⟩, hJF z hz⟩)
  rcases ((isPreconnected_chart_inter hch).image J
    (hJ.continuousOn.mono inter_subset_left)).subset_or_subset hUo hVo hUV (by
    grind) with hSU | hSV
  · have hcl  := closure_minimal (hSU.trans hUV.subset_compl_right) hVo.isClosed_compl
    grind
  · have hcl  := closure_minimal (hSV.trans hUV.symm.subset_compl_right) hUo.isClosed_compl
    grind

private theorem circleDensityCauchy_differentiableOn_of_zero_near
    (g : ℝ → ℂ) (hg : Continuous g) {ζ : ℂ} {d : ℝ} (hd : 0 < d)
    (hzero : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖circleMap 0 1 θ - ζ‖ < d → g θ = 0) :
    DifferentiableOn ℂ (fun w : ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (circleMap 0 1 θ - w))
      (ball ζ (d / 2)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (2 * Real.pi)) hg.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hsep (θ : ℝ) (_hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi))
      (hfar : d ≤ ‖circleMap 0 1 θ - ζ‖) (w : ℂ) (hw : w ∈ ball ζ (d / 2)) :
      d / 2 ≤ ‖circleMap 0 1 θ - w‖ := by
    have hw' : ‖w - ζ‖ < d / 2 := by simp_all [mem_ball, dist_eq_norm]
    have htri : ‖circleMap 0 1 θ - ζ‖ ≤ ‖circleMap 0 1 θ - w‖ + ‖w - ζ‖ := by
      calc
        _ = ‖(circleMap 0 1 θ - w) + (w - ζ)‖ := by ring
        _ ≤ _ := norm_add_le _ _
    linarith
  have hquot (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi))
      (w : ℂ) (hw : w ∈ ball ζ (d / 2)) :
      ‖g θ / (circleMap 0 1 θ - w)‖ ≤ M / (d / 2) := by
    by_cases hn : ‖circleMap 0 1 θ - ζ‖ < d
    · rw [hzero θ hθ hn, zero_div, norm_zero]
      positivity
    · rw [norm_div]
      exact div_le_div₀ hM0 (hM θ hθ) (half_pos hd)
        (hsep θ hθ (le_of_not_gt hn) w hw)
  have hderivBound (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi))
      (w : ℂ) (hw : w ∈ ball ζ (d / 2)) :
      ‖g θ / (circleMap 0 1 θ - w) ^ 2‖ ≤ M / (d / 2) ^ 2 := by
    by_cases hn : ‖circleMap 0 1 θ - ζ‖ < d
    · rw [hzero θ hθ hn, zero_div, norm_zero]
      positivity
    · rw [norm_div, norm_pow]
      exact div_le_div₀ hM0 (hM θ hθ) (sq_pos_of_pos (half_pos hd))
        ((sq_le_sq₀ (half_pos hd).le (norm_nonneg _)).mpr
          (hsep θ hθ (le_of_not_gt hn) w hw))
  intro w₀ hw₀
  have hmeas (w : ℂ) : AEStronglyMeasurable
      (fun θ : ℝ => g θ / (circleMap 0 1 θ - w))
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (hg.measurable.div ((measurable_circleMap 0 1).sub measurable_const)).aestronglyMeasurable
  have hFi : Integrable (fun θ : ℝ => g θ / (circleMap 0 1 θ - w₀))
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
    apply (integrable_const (M / (d / 2))).mono' (hmeas w₀)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    grind
  have hb : ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)),
      ∀ w ∈ ball ζ (d / 2),
        ‖g θ / (circleMap 0 1 θ - w) ^ 2‖ ≤ M / (d / 2) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    grind
  have hdif : ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)),
      ∀ w ∈ ball ζ (d / 2),
        HasDerivAt (fun v : ℂ => g θ / (circleMap 0 1 θ - v))
          (g θ / (circleMap 0 1 θ - w) ^ 2) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    intro w hw
    have hθ' : θ ∈ Icc (0 : ℝ) (2 * Real.pi) := ⟨hθ.1.le, hθ.2⟩
    by_cases hn : ‖circleMap 0 1 θ - ζ‖ < d
    · simp only [hzero θ hθ' hn, zero_div]
      exact hasDerivAt_const w 0
    · have hne : circleMap 0 1 θ - w ≠ 0 := norm_pos_iff.mp
        (lt_of_lt_of_le (half_pos hd) (hsep θ hθ' (le_of_not_gt hn) w hw))
      have h := (hasDerivAt_const w (g θ)).div
          ((hasDerivAt_const w (circleMap 0 1 θ)).sub (hasDerivAt_id w)) hne
      simp only [zero_mul, mul_neg, mul_one, zero_sub, neg_neg] at h
      assumption
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))
    (F := fun w θ => g θ / (circleMap 0 1 θ - w))
    (F' := fun w θ => g θ / (circleMap 0 1 θ - w) ^ 2)
    (bound := fun _ : ℝ => M / (d / 2) ^ 2)
    (isOpen_ball.mem_nhds hw₀) (Eventually.of_forall hmeas) hFi
    (hg.measurable.div
      (((measurable_circleMap 0 1).sub measurable_const).pow_const 2)).aestronglyMeasurable
    hb (integrable_const _) hdif
  have ht : HasDerivAt (fun w : ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (circleMap 0 1 θ - w))
      (∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (circleMap 0 1 θ - w₀) ^ 2) w₀ := by
    simp_all [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  exact ht.differentiableAt.differentiableWithinAt

/-- Boundary uniqueness on a genuine open circle patch. The proof
continues the actual Cauchy integral across the patch where its density
vanishes, then uses its exterior zero values and the analytic identity
principle. No reflection theorem or boundary differentiability is a
premise. -/
theorem diffContOnCl_eq_zero_of_circle_patch
    (hG : DiffContOnCl ℂ G (ball 0 1))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {d : ℝ} (hd : 0 < d)
    (hzero : ∀ z ∈ sphere 0 1, ‖z - ζ‖ < d → G z = 0) :
    EqOn G 0 (ball 0 1) := by
  let C  := fun w => circleIntegral (fun z => (z - w)⁻¹ * G z) 0 1
  let g  := fun θ => deriv (circleMap 0 1) θ * G (circleMap 0 1 θ)
  have hCint : C = fun w  =>
      ∫ θ in 0..(2 * Real.pi), g θ / (circleMap 0 1 θ - w) := by
    funext w
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  have hCd : DifferentiableOn ℂ C (ball ζ (d / 2)) := by
    rw [hCint]
    apply circleDensityCauchy_differentiableOn_of_zero_near g (((contDiff_circleMap 0 1).continuous_deriv_one).mul
      (hG.continuousOn_ball.comp_continuous (continuous_circleMap 0 1) fun θ =>
        sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one θ))) hd
    simp_all [g]
  have hCinside (w : ℂ) (hw : w ∈ ball 0 1) :
      C w = 2 * Real.pi * I * G w := by
    simpa only [smul_eq_mul] using hG.circleIntegral_sub_inv_smul hw
  have hCoutside (w : ℂ) (hw : 1 < ‖w‖) : C w = 0 := by
    have hsub : DiffContOnCl ℂ (fun z  => z - w) (ball 0 1) :=
      (differentiable_id.sub_const w).diffContOnCl
    simpa only [Pi.inv_apply, smul_eq_mul] using ((hsub.inv (by
      intro z hz hzw
      have hzn  := mem_closedBall_zero_iff.mp (closure_ball_subset_closedBall hz)
      grind)).smul hG).circleIntegral_eq_zero zero_le_one
  let e := min (d / 4) (1 / 2)
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have hehalf : e < d / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have heone : e < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let wout  := (1 + e) • ζ
  have hwoutn : ‖wout‖ = 1 + e := by
    simp only [wout, norm_smul, Real.norm_eq_abs, hζ, mul_one, abs_of_pos (by linarith : 0 < 1 + e)]
  have hwout : wout ∈ ball ζ (d / 2) := by
    rw [mem_ball, dist_eq_norm]
    have heq : wout - ζ = e • ζ := by
      change (1 + e) • ζ - ζ = e • ζ
      simp [add_smul]
    simp_all [abs_of_pos he]
  let win  := (1 - e) • ζ
  have hwinn : ‖win‖ = 1 - e := by
    simp only [win, norm_smul, Real.norm_eq_abs, hζ, mul_one, abs_of_pos (sub_pos.mpr heone)]
  have hwinD : win ∈ ball 0 1 := by
    simp_all
  have hwinB : win ∈ ball ζ (d / 2) := by
    rw [mem_ball, dist_eq_norm]
    have heq : win - ζ = (-e) • ζ := by
      change (1 - e) • ζ - ζ = (-e) • ζ
      simp [sub_smul]
    simp_all [abs_of_pos he]
  exact hG.differentiableOn.analyticOnNhd isOpen_ball
    |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 1).isPreconnected
      hwinD (by
    filter_upwards [isOpen_ball.mem_nhds hwinD, isOpen_ball.mem_nhds hwinB] with w hwD hwB
    have hz  := (hCinside w hwD).symm.trans (hCd.analyticOnNhd isOpen_ball |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball ζ (d / 2)).isPreconnected hwout (by
    have ho : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [ho.mem_nhds (by simp_all)] with w hw
    simp_all) hwB)
    simp_all)

private theorem unitCircle_mem_slitPlane_of_ne_neg_one {z : ℂ}
    (hz : ‖z‖ = 1) (hne : z ≠ -1) : z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : z.im = 0
  · left
    have hsq : z.re * z.re = 1 := by
      have ht := normSq_eq_norm_sq z
      simp_all [normSq_apply]
    have hrne : z.re ≠ -1 := by
      intro hr
      apply hne
      apply Complex.ext
      all_goals simp_all
    grind
  simp_all

/-- Any nontrivial connected proper subset of the actual unit circle
contains a relatively open circle patch. The argument cut is chosen at
an actual circle point outside the set; no circle-arc premise is used. -/
theorem exists_circle_patch_subset_of_preconnected
    {A : Set ℂ} (hA : IsPreconnected A) (hAs : A ⊆ sphere 0 1)
    {η : ℂ} (hη : ‖η‖ = 1) (hηA : η ∉ A)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ A) (hz₂ : z₂ ∈ A) (h12 : z₁ ≠ z₂) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ z ∈ sphere 0 1, ‖z - ζ‖ < d → z ∈ A := by
  let u  := fun z => -conj η * z
  have hucont : Continuous u := continuous_const.mul continuous_id
  have hηconj : η * conj η = 1 := by
    simp [mul_conj, normSq_eq_norm_sq, hη]
  have hunorm {z : ℂ} (hz : z ∈ sphere 0 1) : ‖u z‖ = 1 := by
    have hzn : ‖z‖ = 1 := by simp_all
    simp [u, hη, hzn]
  have huslit (z : ℂ) (hz : z ∈ A) : u z ∈ slitPlane := by
    apply unitCircle_mem_slitPlane_of_ne_neg_one (hunorm (hAs hz))
    grind
  let f  := fun z => arg (u z)
  have hfconn  := hA.image f (by
    intro z hz
    exact ((continuousAt_arg (huslit z hz)).comp hucont.continuousAt).continuousWithinAt)
  have hf_inj {z w : ℂ} (hz : z ∈ sphere 0 1)
      (hw : w ∈ sphere 0 1) (he : f z = f w) : z = w := by
    have hue  := ext_norm_arg_iff.mpr
      ⟨(hunorm hz).trans (hunorm hw).symm, he⟩
    grind
  have hbuild (a b : ℝ) (hab : a < b) (ha : a ∈ f '' A) (hb : b ∈ f '' A) :
      ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∃ d : ℝ, 0 < d ∧
        ∀ z ∈ sphere 0 1, ‖z - ζ‖ < d → z ∈ A := by
    have hm : (a + b) / 2 ∈ f '' A := hfconn.Icc_subset ha hb ⟨by linarith, by linarith⟩
    obtain ⟨ζ, hζA, hζm⟩ := hm
    have hζs  := hAs hζA
    have hmI : f ζ ∈ Ioo a b := by grind
    obtain ⟨d, hd, hdb⟩ := Metric.mem_nhds_iff.mp ((continuousAt_arg (huslit ζ hζA)).comp hucont.continuousAt (isOpen_Ioo.mem_nhds hmI))
    refine ⟨ζ, by simp_all, d, hd, ?_⟩
    intro z hzs hzn
    have hfz  := hdb (by simpa only [mem_ball, dist_eq_norm] using hzn)
    have hfzim  := hfconn.Icc_subset ha hb ⟨hfz.1.le, hfz.2.le⟩
    grind
  rcases lt_or_gt_of_ne fun he => h12 (hf_inj (hAs hz₁) (hAs hz₂) he) with hlt | hgt
  all_goals grind

/-- The actual continuous Riemann-map extension is injective on the
entire closed disk. Connected frontier fibers cannot contain a circle
arc, by the actual Cauchy continuation uniqueness proved above. -/
theorem riemannMappingClosedExtension_injOn
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω) :
    InjOn (riemannMappingClosedExtension F) (closedBall 0 1) := by
  let G := riemannMappingClosedExtension F
  have hGc  :=
    riemannMappingClosedExtension_continuousOn hb hL hsc F hF hinj himage
  have hEq  := riemannMappingClosedExtension_eqOn F hF
  have hGhol  := hF.congr (fun z hz => hEq hz)
  have hzeroD : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hhalfD : (1 / 2 : ℂ) ∈ ball 0 1 := by
    norm_num
  have hnonconst (p : ℂ) : ¬ EqOn G (fun _ => p) (ball 0 1) := by
    intro he
    have hbad := hinj hzeroD hhalfD ((hEq hzeroD).symm.trans ((he hzeroD).trans ((he hhalfD).symm.trans (hEq hhalfD))))
    simp_all
  intro z hz w hw he
  by_cases hzD : z ∈ ball 0 1
  · exact riemannMappingClosedExtension_eq_of_eq_of_mem_disk hb hL hsc F hF hinj himage hzD hw he
  by_cases hwD : w ∈ ball 0 1
  · exact (riemannMappingClosedExtension_eq_of_eq_of_mem_disk hb hL hsc F hF hinj himage hwD hz he.symm).symm
  by_contra hzw
  let p := G z
  let A := closedBall 0 1 ∩ G ⁻¹' {p}
  have hp  := riemannMappingClosedExtension_mem_frontier hb hL hsc F hF hinj himage (le_antisymm (mem_closedBall_zero_iff.mp hz)
    (le_of_not_gt fun hn => hzD (mem_ball_zero_iff.mpr hn)))
  have hηex : ∃ η : ℂ, ‖η‖ = 1 ∧ η ∉ A := by
    by_contra hno
    push_neg at hno
    exact hnonconst p (fun v hv => sub_eq_zero.mp (diffContOnCl_eq_zero_of_circle_patch (fun v => G v - p) ((DiffContOnCl.mk_ball hGhol hGc).sub_const p)
        (by norm_num : ‖(1 : ℂ)‖ = 1) zero_lt_one (by
          intro v hvs _
          have hvA := hno v (by simp_all)
          grind) hv))
  obtain ⟨η, hη, hηA⟩ := hηex
  obtain ⟨ζ, hζ, d, hd, hpatch⟩ :=
    exists_circle_patch_subset_of_preconnected (riemannMappingClosedExtension_boundary_fiber_connected hb hL hsc F hF hinj himage hp).2 (by
    intro v hv
    have hvD : v ∉ ball 0 1 := by
      rw [hL.1.1.frontier_eq] at hp
      grind
    have hvone  := le_antisymm (mem_closedBall_zero_iff.mp hv.1) (le_of_not_gt fun hn => hvD (mem_ball_zero_iff.mpr hn))
    simp_all) hη hηA ⟨hz, rfl⟩ ⟨hw, he.symm⟩ hzw
  exact hnonconst p (fun v hv => sub_eq_zero.mp (diffContOnCl_eq_zero_of_circle_patch (fun v => G v - p) ((DiffContOnCl.mk_ball hGhol hGc).sub_const p) hζ hd
      (fun v hvs hvn => sub_eq_zero.mpr (hpatch v hvs hvn).2) hv))

/-- The actual closed-disk extension is a homeomorphism onto the
physical closure. Its values are exactly those of the constructed
extension, including every original interior value. -/
theorem exists_riemannMapping_closedDisk_homeomorph
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω) :
    ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure Ω,
      ∀ z : closedBall 0 1, e z = riemannMappingClosedExtension F z := by
  let G := riemannMappingClosedExtension F
  have hGim  :=
    riemannMappingClosedExtension_closed_image hb hL hsc F hF hinj himage
  let f : closedBall (0 : ℂ) 1 → closure Ω := fun z =>
    ⟨G z, hGim ▸ mem_image_of_mem G z.property⟩
  let e  := Equiv.ofBijective f (by
    constructor
    · intro z w he
      apply Subtype.ext
      exact riemannMappingClosedExtension_injOn hb hL hsc F hF hinj himage z.property w.property (congrArg Subtype.val he)
    · intro w
      have hw : (w : ℂ) ∈ G '' closedBall 0 1 := hGim.symm ▸ w.property
      obtain ⟨z, hz, hze⟩ := hw
      exact ⟨⟨z, hz⟩, Subtype.ext hze⟩)
  have hec : Continuous e := (riemannMappingClosedExtension_continuousOn hb hL hsc F hF hinj himage).restrict.subtype_mk _
  exact ⟨hec.homeoOfEquivCompactToT2, fun _ => rfl⟩

end PolyaNeumann

end
