module

public import RequestProject.SmoothBoundaryParamUniqueness
public import RequestProject.LocalConformalAreaOrientation


/-! Synchronize the conformal circle trace with a given physical boundary parameter. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric MeasureTheory Filter Complex
open scoped Topology Real

section

variable {Γ : ℝ → ℂ} (hΓ : ContDiff ℝ 1 Γ) (hper : Function.Periodic Γ (2 * Real.pi)) (hnz : ∀ θ, deriv Γ θ ≠ 0)
include Γ hΓ hper hnz

/-- The canonical arc curve is genuinely C¹: its previously proved inverse
derivative is continuous because the original speed is continuous and nonzero. -/
theorem normalizedArcCurve_contDiff  :
    ContDiff ℝ 1 (normalizedArcCurve hΓ hper hnz) := let σ := ⇑(normalizedArcOrderIso hΓ hper hnz).symm; let a := 2 * π / arcLen Γ (2 * π); have ha := div_pos Real.two_pi_pos (arcLen_period_pos_of_regular hΓ hnz); have hσ := OrderIso.continuous (normalizedArcOrderIso hΓ hper hnz).symm; have hv := Continuous.comp (ContDiff.continuous_deriv_one hΓ) hσ; have hd := Continuous.mul continuous_const (Continuous.norm hv); have hdne := fun t => LT.lt.ne' (mul_pos ha (norm_pos_iff.mpr (hnz (σ t)))); have hformula := funext fun t => HasDerivAt.deriv (normalizedArcCurve_hasDerivAt hΓ hper hnz t); contDiff_one_iff_deriv.mpr ⟨fun t => HasDerivAt.differentiableAt (normalizedArcCurve_hasDerivAt hΓ hper hnz t), Eq.mpr (id (congrArg (fun _a => Continuous _a) hformula)) (Continuous.smul (Continuous.inv₀ hd hdne) hv)⟩

/-- The canonical arc curve has a genuinely nonzero velocity everywhere. -/
theorem normalizedArcCurve_deriv_ne_zero  (t : ℝ) :
    deriv (normalizedArcCurve hΓ hper hnz) t ≠ 0 := by
  apply norm_pos_iff.mp
  rw [normalizedArcCurve_speed hΓ hper hnz]
  exact div_pos (arcLen_period_pos_of_regular hΓ hnz) Real.two_pi_pos

end

private def rebase (τ : ℝ → ℝ) (φ θ : ℝ) : ℝ := τ (θ + φ) - τ φ

private lemma rebase_isC1 {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hlower : ∀ θ, c ≤ deriv τ θ) (hper : ∀ θ, τ (θ + 2 * π) = τ θ + 2 * π)
    (φ : ℝ) : IsC1TraceReparam (rebase τ φ) c := by
  obtain ⟨K, hK⟩ := hτ.lipschitz
  refine ⟨fun x y hxy => sub_le_sub_right (hτ.monotone (add_le_add hxy (le_refl φ))) (τ φ),
    ⟨K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩,
    (hτ.contDiff.comp (contDiff_id.add contDiff_const)).sub contDiff_const,
    by simp [rebase], by simpa [rebase, sub_eq_iff_eq_add, add_comm] using hper φ,
    hτ.lower_pos, Eventually.of_forall (fun θ => ?_)⟩
  · simpa [rebase, Real.dist_eq] using hK.dist_le_mul (x + φ) (y + φ)
  · have hd : HasDerivAt (rebase τ φ) (deriv τ (θ + φ)) θ := by
      show HasDerivAt (fun x => τ (x + φ) - τ φ) _ θ
      simpa only [rebase, Function.comp_def, id, mul_one] using
        ((hτ.contDiff.differentiable_one (θ + φ)).hasDerivAt.comp θ
          ((hasDerivAt_id θ).add_const φ)).sub_const (τ φ)
    rw [hd.deriv]
    exact hlower _

private lemma mul_image_ball {a : ℂ} (ha : ‖a‖ = 1) (r : ℝ) :
    (a * ·) '' ball 0 r = ball 0 r := by
  have h0 : a ≠ 0 := by rintro rfl; simp at ha
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [mem_ball_zero_iff, norm_mul, ha] using hw
  · intro hz
    refine ⟨a⁻¹ * z, ?_, ?_⟩
    · simpa [mem_ball_zero_iff, norm_mul, ha] using hz
    · simp [h0]

/-- Precomposing an analytic chart by a rotation preserves its chart bounds. -/
private def rotateCoordinates {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
    {a : ℂ} (ha : ‖a‖ = 1) : ConformalDiskCoordinates (F ∘ (a * ·)) := by
  have hmem {r : ℝ} {z : ℂ} (hz : z ∈ ball 0 r) : a * z ∈ ball 0 r := by
    simpa [mem_ball_zero_iff, norm_mul, ha] using hz
  have h0 : a ≠ 0 := by rintro rfl; simp at ha
  have hrot (z : ℂ) : HasDerivAt (a * ·) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  have himage : (F ∘ (a * ·)) '' ball 0 1 = F '' ball 0 1 := by
    rw [image_comp, mul_image_ball ha]
  have hnorm (z : ℂ) (hz : z ∈ ball 0 1) :
      ‖deriv (F ∘ (a * ·)) z‖ = ‖deriv F (a * z)‖ := by
    rw [((coords.holomorphic.differentiableAt (isOpen_ball.mem_nhds (hmem hz))).hasDerivAt.comp z
      (hrot z)).deriv, norm_mul, ha, mul_one]
  exact ⟨coords.radius, coords.inverseBound, coords.derivativeBound, coords.one_lt_radius,
    himage.symm ▸ coords.bounded, himage.symm ▸ coords.lipschitz,
    coords.holomorphic_collar.comp (fun z _ => (hrot z).differentiableAt.differentiableWithinAt)
      (fun _ hz => hmem hz),
    fun _ hz _ hw he => mul_left_cancel₀ h0 (coords.injOn_collar (hmem hz) (hmem hw) he),
    fun z hz => (hnorm z hz).symm ▸ coords.lower (a * z) (hmem hz),
    fun z hz => (hnorm z hz).symm ▸ coords.upper_deriv (a * z) (hmem hz)⟩

/-- The normalized arclength lift aligns a rotation of the given chart with `γ`. -/
theorem exists_aligned_coordinates {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball 0 1) γ) :
    ∃ G : ℂ → ℂ, Nonempty (ConformalDiskCoordinates G) ∧ G '' ball 0 1 = F '' ball 0 1 ∧
      ∃ (τ : ℝ → ℝ) (c : ℝ) (K : NNReal), IsC1TraceReparam τ c ∧
        physicalCircleTrace G = γ ∘ τ ∧ LipschitzWith K (physicalCircleTrace G) := by
  let Γ := physicalCircleTrace F
  let hΓ := coords.trace_contDiff
  let hper := physicalCircleTrace_periodic F
  let hnz := coords.trace_deriv_ne_zero
  obtain ⟨t, _, hs⟩ := exists_boundaryParam_shift_of_bounded_domain coords.bounded coords.lipschitz.1
    (localConformal_normalizedArcCurve_isBoundaryParam coords)
    (normalizedArcCurve_contDiff hΓ hper hnz) (normalizedArcCurve_deriv_ne_zero hΓ hper hnz) hγ
  let φ := (normalizedArcOrderIso hΓ hper hnz).symm t
  have ht : normalizedArcReparam Γ φ = t := (normalizedArcOrderIso hΓ hper hnz).apply_symm_apply t
  let a := circleMap 0 1 φ
  have ha : ‖a‖ = 1 := by simp [a]
  let G := F ∘ (a * ·)
  let d : ConformalDiskCoordinates G := rotateCoordinates coords ha
  obtain ⟨c, hp, hlower, hperiod⟩ := exists_isC1TraceReparam_normalizedArc hΓ hper hnz
  obtain ⟨K, hK⟩ := exists_periodic_C1_density_lipschitz _ d.trace_contDiff (physicalCircleTrace_periodic G)
  refine ⟨G, ⟨d⟩, ?_, rebase (normalizedArcReparam Γ) φ, c, K,
    rebase_isC1 hp hlower hperiod φ, funext fun θ => ?_, hK⟩
  · change (F ∘ (a * ·)) '' ball 0 1 = _
    rw [image_comp, mul_image_ball ha]
  · change F (circleMap 0 1 φ * circleMap 0 1 θ) = γ (rebase (normalizedArcReparam Γ) φ θ)
    rw [circleMap_zero_mul, one_mul, add_comm φ, hs]
    change Γ (θ + φ) = normalizedArcCurve hΓ hper hnz (rebase (normalizedArcReparam Γ) φ θ + t)
    rw [rebase, ht, sub_add_cancel]
    exact normalizedArcCurve_factorization hΓ hper hnz (θ + φ)

end PolyaNeumann

end
