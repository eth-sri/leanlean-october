module

public import RequestProject.LocalConformalFourierTaylor
public import RequestProject.LocalConformalArcFactorization
public import RequestProject.RiemannMappingInterior
public import RequestProject.RiemannMappingBoundaryParamRegularity

/-!
# A real smooth collar from the actual regular conformal boundary trace

The Fourier collar agrees with the given holomorphic map on the whole
closed disk. Injectivity supplies the nonzero interior derivative; the
actual regular angular trace supplies the nonzero boundary differential.
Compactness then supplies genuine upper and lower bounds and the certified
local inverse theorem constructs a smooth inverse on a neighborhood.

The collar is real smooth on the plane. Complex holomorphicity is claimed
only on the original open disk. The first theorem package is compositional:
its regular trace inputs must come from the actual boundary regularity
chain before it is instantiated under the original domain hypotheses.
This module is part of the verified dependency chain.
-/

@[expose] public section
noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory
open scoped Topology ContDiff

/-- Genuine supplied smooth conformal coordinates under the original
bounded smooth simply-connected domain assumptions. The map, real smooth
collar, differential bounds and smooth neighborhood inverse are all
conclusions. This changes no hypothesis of the original strict theorem. -/
local notation "Φ0" => closedBall 0 1

local notation "Φ1" => ball 0 1

theorem exists_smoothConformal_coordinates Ω
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ (R C K : ℝ) (F : ℂ → ℂ) (e : OpenPartialHomeomorph ℂ ℂ),
      1 < R ∧ 0 < C ∧ 0 < K ∧
      ContDiffOn ℝ ∞ F (ball 0 R) ∧
      DifferentiableOn ℂ F (Φ1) ∧
      InjOn F (Φ0) ∧ F '' Φ1 = Ω ∧
      (∀ z ∈ Φ0, fderiv ℝ F z 1 ≠ 0) ∧
      (∀ z ∈ Φ1, 1 ≤ C * ‖deriv F z‖ ^ 2) ∧
      (∀ z ∈ Φ1, ‖fderiv ℝ F z 1‖ ≤ K) ∧
      (e : ℂ → ℂ) = F ∧ Φ0 ⊆ e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      F '' Φ0 = closure Ω ∧ F '' sphere 0 1 = frontier Ω := by
  obtain ⟨F₀, hF₀, hinj₀, himage₀⟩ := exists_interior_conformal_map Ω hS.1.1 hb hsc
  let F := riemannMappingClosedExtension F₀
  have hHF := riemannMappingClosedExtension_eqOn F₀ hF₀
  obtain ⟨hΓ, hΓnz⟩ := riemannMapping_circleTrace_contDiff_of_genuine_inverse_graphs
    hb hS hsc F₀ hF₀ hinj₀ himage₀ (fun _ hp => exists_riemannMapping_genuine_regular_inverse_graph hb hS hsc F₀ hF₀ hinj₀ himage₀ hp)
  have hinj : InjOn F (Φ0) :=
    riemannMappingClosedExtension_injOn hb hS.isLipschitzDomain hsc F₀ hF₀ hinj₀ himage₀
  obtain ⟨G, hGs, hGF, hhol⟩ := exists_smooth_holomorphic_fourier_collar_of_circleTrace F (DiffContOnCl.mk_ball (hF₀.congr fun z hz => hHF hz) (riemannMappingClosedExtension_continuousOn hb hS.isLipschitzDomain hsc F₀ hF₀ hinj₀ himage₀)) hΓ
  have hGinj : InjOn G (Φ0) := fun z hz w hw he =>
    hinj hz hw (by rw [← hGF hz, ← hGF hw, he])
  have hR : (1 : ℝ) < 2 := by norm_num
  have hG₂ : ContDiffOn ℝ ∞ G (ball 0 2) := hGs.contDiffOn
  have hderiv : ∀ {z}, z ∈ Φ1 → fderiv ℝ G z 1 = deriv G z := by
    intro z hz
    rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
    change fderiv ℂ G z 1 = _
    rw [fderiv_eq_deriv_mul, mul_one]
  have hnz : ∀ z ∈ Φ0, fderiv ℝ G z 1 ≠ 0 := by
    intro z hz
    rcases lt_or_eq_of_le (by simpa using hz : ‖z‖ ≤ 1) with hzlt | hzeq
    · have hzD : z ∈ Φ1 := by simpa using hzlt
      rw [hderiv hzD]
      exact RiemannInterior.deriv_ne_zero_of_injOn isOpen_ball hhol
        (hGinj.mono ball_subset_closedBall) hzD
    · have hθ : circleMap 0 1 z.arg = z := by
        simpa [circleMap_zero, hzeq] using Complex.norm_mul_exp_arg_mul_I z
      exact fun hn => hΓnz z.arg (by rw [show deriv (physicalCircleTrace F) z.arg = fderiv ℝ G z 1 * (z * Complex.I) by
        simpa [(funext fun θ => hGF (circleMap_mem_closedBall 0 (by norm_num) θ) : physicalCircleTrace G = physicalCircleTrace F), hθ] using localConformal_circleTrace_deriv hR G hG₂ hhol z.arg, hn, zero_mul])
  have hcont : ContinuousOn (fun z => ‖fderiv ℝ G z 1‖) (Φ0) :=
    ((hGs.continuous_fderiv (by simp)).clm_apply continuous_const).norm.continuousOn
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall 0 1).exists_isMinOn ⟨0, by simp⟩ hcont
  have hp : 0 < ‖fderiv ℝ G z₀ 1‖ := norm_pos_iff.mpr (hnz z₀ hz₀)
  obtain ⟨B, hB⟩ := (isCompact_closedBall 0 1).exists_bound_of_continuousOn hcont
  obtain ⟨e, he, hsource, _, hes⟩ := exists_localConformalInverse hR G hG₂ hhol hGinj hnz
  refine ⟨2, (‖fderiv ℝ G z₀ 1‖ ^ 2)⁻¹, max B 1, G, e, hR, by positivity,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _), hG₂, hhol, hGinj,
    (hGF.mono ball_subset_closedBall).image_eq.trans (hHF.image_eq.trans himage₀), hnz,
    fun z hz => ?_, fun z hz => ?_, he, hsource, hes,
    hGF.image_eq.trans (riemannMappingClosedExtension_closed_image hb hS.isLipschitzDomain hsc F₀ hF₀ hinj₀ himage₀),
    (hGF.mono sphere_subset_closedBall).image_eq.trans (riemannMappingClosedExtension_sphere_image hb hS.isLipschitzDomain hsc F₀ hF₀ hinj₀ himage₀)⟩
  · rw [← hderiv hz]
    exact (inv_mul_cancel₀ (by positivity)).symm.le.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hmin (ball_subset_closedBall hz)) 2) (inv_nonneg.mpr (sq_nonneg _)))
  · have hb' := hB z (ball_subset_closedBall hz)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb'
    exact hb'.trans (le_max_left _ _)

end PolyaNeumann
end
