module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.RiemannMappingCapWinding
public import Mathlib.Topology.ExtendFrom
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Homeomorph.Lemmas
public import RequestProject.LocalConformalBoundaryGeometry
public import RequestProject.PlanarNotation

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

section

variable (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F unitDisk)

include F in
/-- The actual full-approach extension of the interior conformal map.
Its continuity on the closed disk is proved below from the physical
domain hypotheses. Values outside the closed disk are immaterial. -/
def riemannMappingClosedExtension : ℂ → ℂ :=
  extendFrom unitDisk F

include hF in
/-- The true extension retains every value of the supplied interior map. -/
theorem riemannMappingClosedExtension_eqOn :
    EqOn (riemannMappingClosedExtension F) F unitDisk := by
  intro z hz
  exact extendFrom_extends hF.continuousOn z hz

/-- The full boundary limit supplies convergence at every closed-disk
point; interior points use the actual holomorphic map's continuity. -/
theorem riemannMapping_exists_limit_closedDisk
    {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : LipschitzUniformization Ω F)
    {z : ℂ} (hz : z ∈ closedDisk) :
    ∃ p : ℂ, Tendsto F (𝓝[unitDisk] z) (𝓝 p) := by
  have hn  := mem_closedBall_zero_iff.mp hz
  rcases eq_or_lt_of_le hn with hn | hn
  · obtain ⟨p, hp, _⟩ := riemannMapping_exists_unique_boundary_limit hΦ hn
    exact ⟨p, hp.2⟩
  · exact ⟨F z, hΦ.holomorphic.continuousOn z (mem_ball_zero_iff.mpr hn)⟩

/-- The actual closed-disk extension is continuous at boundary points
with respect to all closed-disk approaches, not only interior rays. -/
theorem riemannMappingClosedExtension_continuousOn
    {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : LipschitzUniformization Ω F) :
    ContinuousOn (riemannMappingClosedExtension F) closedDisk := by
  apply continuousOn_extendFrom
  · rw [closure_ball 0 one_ne_zero]
  · grind [riemannMapping_exists_limit_closedDisk]

/-- Every actual boundary value is in the physical frontier. This
uses the previously constructed full limit, including its interior
inverse exclusion of an interior image limit. -/
theorem riemannMappingClosedExtension_mem_frontier
    {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : LipschitzUniformization Ω F)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) : riemannMappingClosedExtension F ζ ∈ frontier Ω := by
  obtain ⟨p, hp, _⟩ := riemannMapping_exists_unique_boundary_limit hΦ hζ
  have hζcl : ζ ∈ closure unitDisk := by
    rw [closure_ball 0 one_ne_zero, mem_closedBall_zero_iff, hζ]
  have he : riemannMappingClosedExtension F ζ = p := extendFrom_eq hζcl hp.2
  simp [*]

include hF in
/-- The extension has exactly the original open-disk physical image. -/
theorem riemannMappingClosedExtension_open_image :
    riemannMappingClosedExtension F '' unitDisk = F '' unitDisk :=
  (riemannMappingClosedExtension_eqOn F hF).image_eq

end

/-- The compact closed-disk image is exactly the closure of the actual
physical domain, obtained without boundary injectivity. -/
theorem riemannMappingClosedExtension_closed_image
    {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : LipschitzUniformization Ω F) :
    riemannMappingClosedExtension F '' closedDisk = closure Ω := by
  rw [unitDisk_closed_image_eq_closure _
    (riemannMappingClosedExtension_continuousOn hΦ),
    riemannMappingClosedExtension_open_image F hΦ.holomorphic, hΦ.image]

/-- The extension maps the actual unit circle onto the entire physical
frontier. Surjectivity follows from the compact image identity; an
interior source point cannot map to a frontier point. -/
theorem riemannMappingClosedExtension_sphere_image
    {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : LipschitzUniformization Ω F) :
    riemannMappingClosedExtension F '' diskSphere = frontier Ω := by
  apply Subset.antisymm
  · rintro w ⟨ζ, hζ, rfl⟩
    exact riemannMappingClosedExtension_mem_frontier hΦ
      (by simpa only [mem_sphere, dist_zero_right] using hζ)
  · intro w hw
    have hwcl := frontier_subset_closure hw
    rw [← riemannMappingClosedExtension_closed_image hΦ] at hwcl
    obtain ⟨z, hz, he⟩ := hwcl
    refine ⟨z, ?_, he⟩
    have hn  := mem_closedBall_zero_iff.mp hz
    rcases eq_or_lt_of_le hn with hn | hn
    · simpa using hn
    · have hzD  := mem_ball_zero_iff.mpr hn
      have hwΩ : w ∈ Ω := by
        rw [← hΦ.image]
        exact ⟨z, hzD, (riemannMappingClosedExtension_eqOn F hΦ.holomorphic hzD).symm.trans he⟩
      rw [hΦ.lipschitz.1.1.frontier_eq] at hw
      exact False.elim (hw.2 hwΩ)

/-- On the closed disk the actual interior image points have exactly
the original interior source points as preimages. -/
theorem riemannMappingClosedExtension_mem_domain_iff
    {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : LipschitzUniformization Ω F)
    {z : ℂ} (hz : z ∈ closedDisk) :
    riemannMappingClosedExtension F z ∈ Ω ↔ z ∈ unitDisk := by
  constructor
  · intro hzin
    have hn  := mem_closedBall_zero_iff.mp hz
    rcases eq_or_lt_of_le hn with hn | hn
    · have hfront := riemannMappingClosedExtension_mem_frontier hΦ hn
      rw [hΦ.lipschitz.1.1.frontier_eq] at hfront
      exact False.elim (hfront.2 hzin)
    · exact mem_ball_zero_iff.mpr hn
  · intro hzD
    rw [riemannMappingClosedExtension_eqOn F hΦ.holomorphic hzD, ← hΦ.image]
    exact mem_image_of_mem F hzD

/-- The extension is injective whenever one of its source points is
interior. The only remaining injectivity question concerns two distinct
points of the unit circle. -/
theorem riemannMappingClosedExtension_eq_of_eq_of_mem_disk
    {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : LipschitzUniformization Ω F)
    {z w : ℂ} (hz : z ∈ unitDisk) (hw : w ∈ closedDisk)
    (he : riemannMappingClosedExtension F z = riemannMappingClosedExtension F w) : z = w := by
  have hzΩ  :=
    (riemannMappingClosedExtension_mem_domain_iff hΦ
      (ball_subset_closedBall hz)).mpr hz
  have hwD  :=
    (riemannMappingClosedExtension_mem_domain_iff hΦ hw).mp (he ▸ hzΩ)
  exact hΦ.injective hz hwD (by
    rw [riemannMappingClosedExtension_eqOn F hΦ.holomorphic hz,
      riemannMappingClosedExtension_eqOn F hΦ.holomorphic hwD] at he
    exact he)

/-- A physical frontier fiber of the actual continuous extension is
connected. Compactness selects a physical chart whose entire interior
inverse image lies in any prescribed neighborhood of the fiber; the
true connected graph region cannot split between disjoint neighborhoods.
No monotonicity or connected-fiber premise is assumed. -/
theorem riemannMappingClosedExtension_boundary_fiber_connected
    {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : LipschitzUniformization Ω F)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    IsConnected (closedDisk ∩ riemannMappingClosedExtension F ⁻¹' {p}) := by
  let G := riemannMappingClosedExtension F
  let A := closedDisk ∩ G ⁻¹' {p}
  have hGc  :=
    riemannMappingClosedExtension_continuousOn hΦ
  have hEq : EqOn G F unitDisk := riemannMappingClosedExtension_eqOn F hΦ.holomorphic
  have hAc : IsClosed A := hGc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hAk  :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hAc inter_subset_left
  have hAne : A.Nonempty := by
    have hpim : p ∈ G '' diskSphere := by
      rw [riemannMappingClosedExtension_sphere_image hΦ]
      exact hp
    obtain ⟨ζ, hζ, he⟩ := hpim
    exact ⟨ζ, sphere_subset_closedBall hζ, he⟩
  refine ⟨hAne, ?_⟩
  apply isPreconnected_iff_subset_of_disjoint_closed.mpr
  intro u v hu hv hAuv hAdisj
  have hKu  := hAk.inter_right hu
  have hKv  := hAk.inter_right hv
  have hKdisj : Disjoint (A ∩ u) (A ∩ v) := by
    apply Set.disjoint_left.mpr
    intro z hzu hzv
    have hz : z ∈ A ∩ (u ∩ v) := ⟨hzu.1, hzu.2, hzv.2⟩
    rw [hAdisj] at hz
    exact hz
  obtain ⟨U, V, hUo, hVo, hKuU, hKvV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact hKu hKv hKdisj
  have hAUV : A ⊆ U ∪ V := by
    grind
  let T := closedDisk \ (U ∪ V)
  have hTk  := (isCompact_closedBall (0 : ℂ) 1).diff (hUo.union hVo)
  have hGTk  := hTk.image_of_continuousOn (hGc.mono diff_subset)
  have hpnot : p ∉ G '' T := by
    grind
  obtain ⟨d, hd, hdball⟩ := Metric.isOpen_iff.mp hGTk.isClosed.isOpen_compl p hpnot
  obtain ⟨c, r, h, KC, f, hch, hBball⟩ := exists_small_chart hΦ.lipschitz hp hd
  let B := chartBox p c r h
  have hBo  := isOpen_chartBox p c r h
  have hpB  := hch.center_mem_box
  obtain ⟨J, hJ, hJm, hJF, hFJ⟩ := RiemannInterior.exists_holomorphic_inverse isOpen_ball hΦ.holomorphic hΦ.injective
  rw [hΦ.image] at hJ hJm hFJ
  let S := J '' (Ω ∩ B)
  have hSc  := (isPreconnected_chart_inter hch).image J
    (hJ.continuousOn.mono inter_subset_left)
  have hSclosedDisk : S ⊆ closedDisk := by
    rintro z ⟨w, hw, rfl⟩
    exact ball_subset_closedBall (hJm hw.1)
  have hSG : MapsTo G S B := by
    rintro z ⟨w, hw, rfl⟩
    rw [hEq (hJm hw.1), hFJ w hw.1]
    exact hw.2
  have hSUV : S ⊆ U ∪ V := by
    intro z hz
    by_contra hn
    have hzim : G z ∈ G '' T := ⟨z, ⟨hSclosedDisk hz, hn⟩, rfl⟩
    exact hdball (hBball (hSG hz)) hzim
  have hAcl : A ⊆ closure S := by
    intro ζ hζ
    have hζcl : ζ ∈ closure unitDisk := by
      rw [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)]
      exact hζ.1
    letI  := mem_closure_iff_nhdsWithin_neBot.mp hζcl
    have hlim : Tendsto F (𝓝[unitDisk] ζ) (𝓝 p) := by
      have ht := tendsto_extendFrom (riemannMapping_exists_limit_closedDisk hΦ hζ.1)
      change Tendsto F (𝓝[unitDisk] ζ) (𝓝 (G ζ)) at ht
      rw [show G ζ = p from hζ.2] at ht
      exact ht
    have heB := hlim.eventually (hBo.mem_nhds hpB)
    have heS : ∀ᶠ z in 𝓝[unitDisk] ζ, z ∈ S := by
      filter_upwards [self_mem_nhdsWithin, heB] with z hz hzB
      exact ⟨F z, ⟨hΦ.image ▸ mem_image_of_mem F hz, hzB⟩, hJF z hz⟩
    exact mem_closure_of_tendsto
      ((tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 ζ) (𝓝 ζ)).mono_left nhdsWithin_le_nhds) heS
  rcases hSc.subset_or_subset hUo hVo hUV hSUV with hSU | hSV
  · left
    have hcl  := closure_minimal (hSU.trans hUV.subset_compl_right) hVo.isClosed_compl
    intro z hz
    rcases hAuv hz with hzu | hzv
    · exact hzu
    · exact False.elim (hcl (hAcl hz) (hKvV ⟨hz, hzv⟩))
  · right
    have hcl  := closure_minimal (hSV.trans hUV.symm.subset_compl_right) hUo.isClosed_compl
    intro z hz
    rcases hAuv hz with hzu | hzv
    · exact False.elim (hcl (hAcl hz) (hKuU ⟨hz, hzu⟩))
    · exact hzv

private theorem circleDensityCauchy_differentiableOn_of_zero_near
    (g : ℝ → ℂ) (hg : Continuous g) {ζ : ℂ} {d : ℝ} (hd : 0 < d)
    (hzero : ∀ θ ∈ angleInterval,
      ‖unitCirclePt θ - ζ‖ < d → g θ = 0) :
    DifferentiableOn ℂ (fun w : ℂ =>
      ∫ₚ θ, g θ / (unitCirclePt θ - w))
      (ball ζ (d / 2)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
     hg.continuousOn
  have hM0  := (norm_nonneg (g 0)).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hsep (θ : ℝ) (_hθ : θ ∈ angleInterval)
      (hfar : d ≤ ‖unitCirclePt θ - ζ‖) (w : ℂ) (hw : w ∈ ball ζ (d / 2)) :
      d / 2 ≤ ‖unitCirclePt θ - w‖ := by
    have hw' : ‖w - ζ‖ < d / 2 := by simpa only [mem_ball, dist_eq_norm] using hw
    have htri : ‖unitCirclePt θ - ζ‖ ≤ ‖unitCirclePt θ - w‖ + ‖w - ζ‖ := by
      calc
        _ = ‖(unitCirclePt θ - w) + (w - ζ)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    linarith
  have hquot (θ : ℝ) (hθ : θ ∈ angleInterval)
      (w : ℂ) (hw : w ∈ ball ζ (d / 2)) :
      ‖g θ / (unitCirclePt θ - w)‖ ≤ M / (d / 2) := by
    by_cases hn : ‖unitCirclePt θ - ζ‖ < d
    · rw [hzero θ hθ hn, zero_div, norm_zero]
      positivity
    · rw [norm_div]
      bound
  have hderivBound (θ : ℝ) (hθ : θ ∈ angleInterval)
      (w : ℂ) (hw : w ∈ ball ζ (d / 2)) :
      ‖g θ / (unitCirclePt θ - w) ^ 2‖ ≤ M / (d / 2) ^ 2 := by
    by_cases hn : ‖unitCirclePt θ - ζ‖ < d
    · rw [hzero θ hθ hn, zero_div, norm_zero]
      positivity
    · rw [norm_div, norm_pow]
      bound
  intro w₀ hw₀
  have hmeas (w : ℂ) : AEStronglyMeasurable
      (fun θ : ℝ => g θ / (unitCirclePt θ - w))
      angleMeasure :=
    (hg.measurable.div ((measurable_circleMap 0 1).sub measurable_const)).aestronglyMeasurable
  
  
  have hdif : ∀ᵐ θ ∂angleMeasure,
      ∀ w ∈ ball ζ (d / 2),
        HasDerivAt (fun v : ℂ => g θ / (unitCirclePt θ - v))
          (g θ / (unitCirclePt θ - w) ^ 2) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    intro w hw
    have hθ' : θ ∈ angleInterval := (by grind)
    by_cases hn : ‖unitCirclePt θ - ζ‖ < d
    · simp [hzero θ hθ' hn, zero_div]
      exact hasDerivAt_const w 0
    · 
      have h := (hasDerivAt_const w (g θ)).div
          ((hasDerivAt_const w (unitCirclePt θ)).sub (hasDerivAt_id w)) (norm_pos_iff.mp
            (lt_of_lt_of_le (half_pos hd) (hsep θ hθ' (le_of_not_gt hn) w hw)))
      simp at h
      exact h
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    
    
    
    
    (isOpen_ball.mem_nhds hw₀) (Eventually.of_forall hmeas) (by
      apply (integrable_const (M / (d / 2))).mono' (hmeas w₀)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
      exact hquot θ ⟨hθ.1.le, hθ.2⟩ w₀ hw₀)
    (hg.measurable.div
      (((measurable_circleMap 0 1).sub measurable_const).pow_const 2)).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
      exact hderivBound θ ⟨hθ.1.le, hθ.2⟩) (integrable_const _) hdif
  have ht : HasDerivAt (fun w : ℂ =>
      ∫ₚ θ, g θ / (unitCirclePt θ - w))
      (∫ₚ θ, g θ / (unitCirclePt θ - w₀) ^ 2) w₀ := by
    simpa only [intervalIntegral.integral_of_le Real.two_pi_pos.le] using hdiff.2
  exact ht.differentiableAt.differentiableWithinAt

/-- Boundary uniqueness on a genuine open circle patch. The proof
continues the actual Cauchy integral across the patch where its density
vanishes, then uses its exterior zero values and the analytic identity
principle. No reflection theorem or boundary differentiability is a
premise. -/
theorem diffContOnCl_eq_zero_of_circle_patch
    (G : ℂ → ℂ) (hG : DiffContOnCl ℂ G unitDisk)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {d : ℝ} (hd : 0 < d)
    (hzero : ∀ z ∈ diskSphere, ‖z - ζ‖ < d → G z = 0) :
    EqOn G 0 unitDisk := by
  let C  := fun w => circleIntegral (fun z => (z - w)⁻¹ * G z) 0 1
  let g  := fun θ => deriv unitCirclePt θ * G (unitCirclePt θ)
  
  have hgc  :=
    ((contDiff_circleMap 0 1).continuous_deriv_one).mul
      (hG.continuousOn_ball.comp_continuous (continuous_circleMap 0 1) (by norm_num))
  have hCint : C = fun w : ℂ =>
      ∫ₚ θ, g θ / (unitCirclePt θ - w) := by
    funext w
    dsimp [g]
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  have hCd : DifferentiableOn ℂ C (ball ζ (d / 2)) := by
    rw [hCint]
    apply circleDensityCauchy_differentiableOn_of_zero_near g hgc hd
    intro θ _hθ hn
    dsimp [g]
    simp [*]
  have hCinside (w : ℂ) (hw : w ∈ unitDisk) := hG.circleIntegral_sub_inv_smul hw
  have hCoutside (w : ℂ) (hw : 1 < ‖w‖) : C w = 0 := by
    
    
    have hquot := ((((differentiable_id : Differentiable ℂ (fun z : ℂ => z)).sub_const w).diffContOnCl).inv (by
      intro z hz hzw
      have hzn  := mem_closedBall_zero_iff.mp (closure_ball_subset_closedBall hz)
      have he  := sub_eq_zero.mp hzw
      exact (not_le_of_gt hw) (he ▸ hzn))).smul hG
    exact hquot.circleIntegral_eq_zero zero_le_one
  let e := min (d / 4) halfOrder
  have he : 0 < e := (by positivity)
  have hehalf : e < d / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have heone : e < 1 := (by bound)
  let wout  := (1 + e) • ζ
  have hwoutn : ‖wout‖ = 1 + e := by
    simp only [wout, norm_smul, Real.norm_eq_abs, hζ, mul_one, abs_of_pos (by linarith : 0 < 1 + e)]
  have hwout : wout ∈ ball ζ (d / 2) := by
    rw [mem_ball, dist_eq_norm]
    have heq : wout - ζ = e • ζ := by
      change (1 + e) • ζ - ζ = e • ζ
      simp [add_smul]
    rw [heq, norm_smul, hζ, mul_one, Real.norm_eq_abs, abs_of_pos he]
    exact hehalf
  have hCevent : C =ᶠ[𝓝 wout] 0 := by
    have ho : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [ho.mem_nhds (by simp [*])] with w hw
    exact hCoutside w hw
  
  let win  := (1 - e) • ζ
  have hwinn : ‖win‖ = 1 - e := by
    simp only [win, norm_smul, Real.norm_eq_abs, hζ, mul_one, abs_of_pos (sub_pos.mpr heone)]
  have hwinD : win ∈ unitDisk := by
    simp [*]
  have hwinB : win ∈ ball ζ (d / 2) := by
    rw [mem_ball, dist_eq_norm]
    have heq : win - ζ = (-e) • ζ := by
      change (1 - e) • ζ - ζ = (-e) • ζ
      simp [sub_smul]
    rw [heq, norm_smul, hζ, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos he]
    exact hehalf
  
  have hGevent : G =ᶠ[𝓝 win] 0 := by
    filter_upwards [isOpen_ball.mem_nhds hwinD, isOpen_ball.mem_nhds hwinB] with w hwD hwB
    have hz  := (hCinside w hwD).symm.trans ((hCd.analyticOnNhd isOpen_ball |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball ζ (d / 2)).isPreconnected hwout hCevent) hwB)
    exact (mul_eq_zero.mp hz).resolve_left (by
      simp)
  exact hG.differentiableOn.analyticOnNhd isOpen_ball
    |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 1).isPreconnected
      hwinD hGevent

private theorem unitCircle_mem_slitPlane_of_ne_neg_one {z : ℂ}
    (hz : ‖z‖ = 1) (hne : z ≠ -1) : z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : z.im = 0
  · left
    have hsq : z.re * z.re = 1 := by
      have ht := normSq_eq_norm_sq z
      rw [normSq_apply, hz, him] at ht
      nlinarith
    have hrne : z.re ≠ -1 := by
      intro hr
      apply hne
      apply Complex.ext
      · exact hr
      · simpa using him
    grind [mul_self_eq_mul_self_iff.mp, zero_lt_one]
  · exact Or.inr him

/-- Any nontrivial connected proper subset of the actual unit circle
contains a relatively open circle patch. The argument cut is chosen at
an actual circle point outside the set; no circle-arc premise is used. -/
theorem exists_circle_patch_subset_of_preconnected
    {A : Set ℂ} (hA : IsPreconnected A) (hAs : A ⊆ diskSphere)
    {η : ℂ} (hη : ‖η‖ = 1) (hηA : η ∉ A)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ A) (hz₂ : z₂ ∈ A) (h12 : z₁ ≠ z₂) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ z ∈ diskSphere, ‖z - ζ‖ < d → z ∈ A := by
  let u  := fun z => -conj η * z
  have hucont : Continuous u := continuous_const.mul continuous_id
  have hηconj : η * conj η = 1 := by
    simp [mul_conj, normSq_eq_norm_sq, hη]
  have huinv (z : ℂ) : (-η) * u z = z := by
    grind
  have hunorm {z : ℂ} (hz : z ∈ diskSphere) : ‖u z‖ = 1 := by
    aesop
  have huslit (z : ℂ) (hz : z ∈ A) : u z ∈ slitPlane := by
    grind [unitCircle_mem_slitPlane_of_ne_neg_one]
  let f  := fun z => arg (u z)
  
  have hfconn  := hA.image f (by
    intro z hz
    exact ((continuousAt_arg (huslit z hz)).comp hucont.continuousAt).continuousWithinAt)
  have hf_inj {z w : ℂ} (hz : z ∈ diskSphere)
      (hw : w ∈ diskSphere) (he : f z = f w) : z = w := by
    grind [ext_norm_arg_iff.mpr]
  
  have hbuild (a b : ℝ) (hab : a < b) (ha : a ∈ f '' A) (hb : b ∈ f '' A) :
      ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∃ d : ℝ, 0 < d ∧
        ∀ z ∈ diskSphere, ‖z - ζ‖ < d → z ∈ A := by
    have hm : (a + b) / 2 ∈ f '' A := hfconn.Icc_subset ha hb ⟨by linarith, by linarith⟩
    obtain ⟨ζ, hζA, hζm⟩ := hm
    have hζs  := hAs hζA
    
    have hmI : f ζ ∈ Ioo a b := by constructor <;> linarith
    obtain ⟨d, hd, hdb⟩ := Metric.mem_nhds_iff.mp (((continuousAt_arg (huslit ζ hζA)).comp hucont.continuousAt) (isOpen_Ioo.mem_nhds hmI))
    refine ⟨ζ, by simpa only [mem_sphere, dist_zero_right] using hζs, d, hd, ?_⟩
    intro z hzs hzn
    have hfz  := hdb (by simpa only [mem_ball, dist_eq_norm] using hzn)
    
    obtain ⟨w, hwA, hwe⟩ := (hfconn.Icc_subset ha hb ⟨hfz.1.le, hfz.2.le⟩)
    have hzw  := hf_inj hzs (hAs hwA) hwe.symm
    simp [*]
  rcases lt_or_gt_of_ne (fun he => h12 (hf_inj (hAs hz₁) (hAs hz₂) he)) with hlt | hgt
  · exact hbuild (f z₁) (f z₂) hlt (mem_image_of_mem f hz₁) (mem_image_of_mem f hz₂)
  · exact hbuild (f z₂) (f z₁) hgt (mem_image_of_mem f hz₂) (mem_image_of_mem f hz₁)

/-- The actual continuous Riemann-map extension is injective on the
entire closed disk. Connected frontier fibers cannot contain a circle
arc, by the actual Cauchy continuation uniqueness proved above. -/
theorem riemannMappingClosedExtension_injOn
    {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : LipschitzUniformization Ω F) :
    InjOn (riemannMappingClosedExtension F) closedDisk := by
  let G := riemannMappingClosedExtension F
  have hGc  :=
    riemannMappingClosedExtension_continuousOn hΦ
  have hEq  := riemannMappingClosedExtension_eqOn F hΦ.holomorphic
  have hGhol  := hΦ.holomorphic.congr (fun z hz => hEq hz)
  have hzeroD : (0 : ℂ) ∈ unitDisk := mem_ball_self zero_lt_one
  have hhalfD : (1 / 2 : ℂ) ∈ unitDisk := by
    norm_num
  have hnonconst (p : ℂ) : ¬ EqOn G (fun _ => p) unitDisk := by
    intro he
    have hval  :=
      (hEq hzeroD).symm.trans ((he hzeroD).trans ((he hhalfD).symm.trans (hEq hhalfD)))
    have hbad := hΦ.injective hzeroD hhalfD hval
    norm_num at hbad
  intro z hz w hw he
  by_cases hzD : z ∈ unitDisk
  · exact riemannMappingClosedExtension_eq_of_eq_of_mem_disk hΦ hzD hw he
  by_cases hwD : w ∈ unitDisk
  · exact (riemannMappingClosedExtension_eq_of_eq_of_mem_disk hΦ hwD hz he.symm).symm
  have hzn  := le_antisymm (mem_closedBall_zero_iff.mp hz)
    (le_of_not_gt fun hn => hzD (mem_ball_zero_iff.mpr hn))
  by_contra hzw
  let p := G z
  let A := closedDisk ∩ G ⁻¹' {p}
  have hp  := riemannMappingClosedExtension_mem_frontier hΦ hzn
  have hAconn  :=
    riemannMappingClosedExtension_boundary_fiber_connected hΦ hp
  have hzA : z ∈ A := ⟨hz, rfl⟩
  have hwA : w ∈ A := ⟨hw, he.symm⟩
  have hAs : A ⊆ diskSphere := by
    intro v hv
    have hvn  := mem_closedBall_zero_iff.mp hv.1
    have hvD : v ∉ unitDisk := by
      intro hvD
      have hpin : p ∈ Ω := by
        rw [← hv.2]
        exact (riemannMappingClosedExtension_mem_domain_iff hΦ hv.1).mpr hvD
      rw [hΦ.lipschitz.1.1.frontier_eq] at hp
      exact hp.2 hpin
    have hvone  := le_antisymm hvn (le_of_not_gt fun hn => hvD (mem_ball_zero_iff.mpr hn))
    simpa using hvone
  have hηex : ∃ η : ℂ, ‖η‖ = 1 ∧ η ∉ A := by
    by_contra hno
    push_neg at hno
    have hGp  :=
      (DiffContOnCl.mk_ball hGhol hGc).sub_const p
    have hzero  :=
      diffContOnCl_eq_zero_of_circle_patch (fun v => G v - p) hGp
        (by norm_num : ‖(1 : ℂ)‖ = 1) zero_lt_one (by
          intro v hvs _
          have hvA := hno v (by simpa only [mem_sphere, dist_zero_right] using hvs)
          exact sub_eq_zero.mpr hvA.2)
    exact hnonconst p (fun v hv => sub_eq_zero.mp (hzero hv))
  obtain ⟨η, hη, hηA⟩ := hηex
  obtain ⟨ζ, hζ, d, hd, hpatch⟩ :=
    exists_circle_patch_subset_of_preconnected hAconn.2 hAs hη hηA hzA hwA hzw
  have hGp  :=
    (DiffContOnCl.mk_ball hGhol hGc).sub_const p
  have hzero  :=
    diffContOnCl_eq_zero_of_circle_patch (fun v => G v - p) hGp hζ hd
      (fun v hvs hvn => sub_eq_zero.mpr (hpatch v hvs hvn).2)
  exact hnonconst p (fun v hv => sub_eq_zero.mp (hzero hv))

/-- The actual closed-disk extension is a homeomorphism onto the
physical closure. Its values are exactly those of the constructed
extension, including every original interior value. -/
theorem exists_riemannMapping_closedDisk_homeomorph
    {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : LipschitzUniformization Ω F) :
    ∃ e : closedDisk ≃ₜ closure Ω,
      ∀ z : closedDisk, (e z : ℂ) = riemannMappingClosedExtension F z := by
  let G := riemannMappingClosedExtension F
  have hGc  :=
    riemannMappingClosedExtension_continuousOn hΦ
  have hGinj  :=
    riemannMappingClosedExtension_injOn hΦ
  have hGim  :=
    riemannMappingClosedExtension_closed_image hΦ
  let f : closedDisk → closure Ω := fun z =>
    ⟨G z, hGim ▸ mem_image_of_mem G z.property⟩
  have hfc : Continuous f := hGc.restrict.subtype_mk _
  have hfb : Function.Bijective f := by
    constructor
    · intro z w he
      apply Subtype.ext
      exact hGinj z.property w.property (congrArg Subtype.val he)
    · intro w
      have hw : (w : ℂ) ∈ G '' closedDisk := hGim.symm ▸ w.property
      obtain ⟨z, hz, hze⟩ := hw
      exact ⟨⟨z, hz⟩, Subtype.ext hze⟩
  letI  :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  let e  := Equiv.ofBijective f hfb
  have hec : Continuous e := hfc
  exact ⟨hec.homeoOfEquivCompactToT2, fun _ => rfl⟩

end PolyaNeumann

end
