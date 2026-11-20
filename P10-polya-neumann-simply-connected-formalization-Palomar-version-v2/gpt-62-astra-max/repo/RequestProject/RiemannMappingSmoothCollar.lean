module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalFourierTaylor
public import RequestProject.LocalConformalArcFactorization
public import RequestProject.RiemannMappingInterior
public import RequestProject.RiemannMappingBoundaryParamRegularity
public import RequestProject.PlanarNotation

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
set_option autoImplicit false
noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory
open scoped Topology ContDiff

/-- Agreement on the closed disk preserves the actual physical trace,
so its derivative is the one used in the boundary nonvanishing argument. -/
theorem smoothCollar_physicalCircleTrace_eq {F G : ℂ → ℂ}
    (hGF : EqOn G F closedDisk) :
    physicalCircleTrace G = physicalCircleTrace F := by
  aesop

theorem smoothCollar_fderiv_one_eq_deriv {G : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ G unitDisk)
    {z : ℂ} (hz : z ∈ unitDisk) : fderiv ℝ G z 1 = deriv G z := by
  rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
  rfl

/-- Every genuine unit-circle point has its actual angular parameter.
No surjectivity of a boundary map is an auxiliary hypothesis. -/
theorem smoothCollar_circleMap_arg {z : ℂ} (hz : ‖z‖ = 1) :
    unitCirclePt z.arg = z := by
  simpa only [circleMap_zero, hz, Complex.ofReal_one, one_mul] using
    Complex.norm_mul_exp_arg_mul_I z

/-- Nonzero angular velocity transfers to the actual collar's boundary
differential through the real chain rule and the proved closed-disk
complex linearity. Interior nonvanishing comes from true injectivity. -/
theorem smoothCollar_fderiv_one_ne_zero_on_closedDisk {R : ℝ} (hR : 1 < R)
    (G F : ℂ → ℂ) (hGs : ContDiffOn ℝ ∞ G (ball (0 : ℂ) R))
    (hGF : EqOn G F closedDisk)
    (hhol : DifferentiableOn ℂ G unitDisk)
    (hinj : InjOn G closedDisk)
    (hΓnz : ∀ θ : ℝ, deriv (physicalCircleTrace F) θ ≠ 0) :
    ∀ z ∈ closedDisk, fderiv ℝ G z 1 ≠ 0 := by
  intro z hz
  have hzNorm : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
  rcases lt_or_eq_of_le hzNorm with hzlt | hzeq
  · have hzD : z ∈ unitDisk := by
      simpa only [mem_ball, dist_zero_right] using hzlt
    rw [smoothCollar_fderiv_one_eq_deriv hhol hzD]
    exact RiemannInterior.deriv_ne_zero_of_injOn isOpen_ball hhol
      (hinj.mono ball_subset_closedBall) hzD
  · let θ := z.arg
    have hθ : unitCirclePt θ = z := smoothCollar_circleMap_arg hzeq
    have hd : deriv (physicalCircleTrace F) θ =
        fderiv ℝ G z 1 * (z * Complex.I) := by
      simpa only [smoothCollar_physicalCircleTrace_eq hGF, hθ] using
        localConformal_circleTrace_deriv ⟨hR, G, hGs⟩ hhol θ
    grind

/-- The two constants are actual compact bounds on the fixed collar.
The positive lower bound holds on the closed disk, including its boundary. -/
theorem exists_smoothCollar_closed_differential_bounds (G : ℂ → ℂ)
    (hGs : ContDiff ℝ ∞ G)
    (hnz : ∀ z ∈ closedDisk, fderiv ℝ G z 1 ≠ 0) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      (∀ z ∈ closedDisk, 1 ≤ C * ‖fderiv ℝ G z 1‖ ^ 2) ∧
      (∀ z ∈ closedDisk, ‖fderiv ℝ G z 1‖ ≤ K) := by
  have hcont : ContinuousOn (fun z : ℂ => ‖fderiv ℝ G z 1‖)
      closedDisk :=
    ((hGs.continuous_fderiv (by simp)).clm_apply continuous_const).norm.continuousOn
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall 0 1).exists_isMinOn
    ⟨0, by simp⟩ hcont
  have hp : 0 < ‖fderiv ℝ G z₀ 1‖ := norm_pos_iff.mpr (hnz z₀ hz₀)
  obtain ⟨B, hB⟩ := (isCompact_closedBall 0 1).exists_bound_of_continuousOn hcont
  refine ⟨(‖fderiv ℝ G z₀ 1‖ ^ 2)⁻¹, max B 1, by positivity,
    (by positivity), ?_, ?_⟩
  · intro z hz
    
    calc
      1 = (‖fderiv ℝ G z₀ 1‖ ^ 2)⁻¹ * ‖fderiv ℝ G z₀ 1‖ ^ 2 :=
        (inv_mul_cancel₀ (by positivity)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hmin hz) 2) ((by positivity))
  · intro z hz
    have hb := hB z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
    simp [*]

/-- The exact supplied-coordinate package is constructed from the real
regularity of the actual closed-map trace. No collar, inverse, differential
lower bound or exterior holomorphicity is included in the premises. -/
theorem exists_smoothConformal_collar_of_regular_circleTrace
    (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F unitDisk)
    (hinj : InjOn F closedDisk)
    (hΓ : ContDiff ℝ ∞ (physicalCircleTrace F))
    (hΓnz : ∀ θ : ℝ, deriv (physicalCircleTrace F) θ ≠ 0) :
    ∃ (G : ℂ → ℂ) (e : OpenPartialHomeomorph ℂ ℂ),
      ContDiff ℝ ∞ G ∧ EqOn G F closedDisk ∧ DifferentiableOn ℂ G unitDisk ∧
      (∀ z ∈ closedDisk, fderiv ℝ G z 1 ≠ 0) ∧ (e : ℂ → ℂ) = G ∧
      closedDisk ⊆ e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨G, hGs, hGF, hhol⟩ :=
    exists_smooth_holomorphic_fourier_collar_of_circleTrace F hF hΓ
  have hGinj : InjOn G closedDisk := by
    intro z hz w hw he
    apply hinj hz hw
    rw [← hGF hz, ← hGF hw]
    exact he
  have hR : (1 : ℝ) < 2 := by norm_num
  have hG₂ : ContDiffOn ℝ ∞ G (ball (0 : ℂ) 2) := hGs.contDiffOn
  have hnz := smoothCollar_fderiv_one_ne_zero_on_closedDisk hR G F hG₂ hGF hhol hGinj hΓnz
  obtain ⟨e, he, hsource, _, hes⟩ := exists_localConformalInverse ⟨hR, G, hG₂⟩ hhol hGinj hnz
  exact ⟨G, e, hGs, hGF, hhol, hnz, he, hsource, hes⟩

/-- A uniformization of a smooth domain has smooth coordinates which agree
with the original map throughout the disk and with its actual boundary extension. -/
theorem SmoothUniformization.coordinates {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : SmoothUniformization Ω F) :
    ∃ Φ : DiskCoordinates, Φ.domain = Ω ∧ EqOn Φ.map (riemannMappingClosedExtension F) closedDisk ∧
      EqOn Φ.map F unitDisk ∧ Φ.map '' closedDisk = closure Ω ∧ Φ.map '' diskSphere = frontier Ω := by
  let H := riemannMappingClosedExtension F
  have hHF := riemannMappingClosedExtension_eqOn F hΦ.holomorphic
  have hHs := DiffContOnCl.mk_ball (hΦ.holomorphic.congr fun z hz => hHF hz)
    (riemannMappingClosedExtension_continuousOn hΦ.toLipschitz)
  have hHinj := riemannMappingClosedExtension_injOn hΦ.toLipschitz
  obtain ⟨hΓ, hΓnz⟩ := riemannMapping_circleTrace_contDiff_of_genuine_inverse_graphs hΦ
    (fun _ hp => exists_riemannMapping_genuine_regular_inverse_graph hΦ hp)
  obtain ⟨G, e, hs, hGH, hh, hnz, he, hsource, hes⟩ :=
    exists_smoothConformal_collar_of_regular_circleTrace H hHs hHinj hΓ hΓnz
  have hGF := (hGH.mono ball_subset_closedBall).trans hHF
  have him := hGF.image_eq.trans hΦ.image
  obtain ⟨C, K, _, _, hc, hk⟩ := exists_smoothCollar_closed_differential_bounds G hs hnz
  let Φ : DiskCoordinates := {
    radius := 2, one_lt_radius := by norm_num, map := G, smooth := hs.contDiffOn
    C := C, K := K, bounded := him.symm ▸ hΦ.bounded, lipschitzDomain := him.symm ▸ hΦ.smooth.isLipschitzDomain
    holomorphic := hh, inj := (hΦ.injective.congr hGF.symm), deriv_lower := fun z hz => by
      simpa only [smoothCollar_fderiv_one_eq_deriv hh hz] using hc z (ball_subset_closedBall hz)
    deriv_upper := fun z hz => hk z (ball_subset_closedBall hz)
    chart := e, chart_eq := he, source := hsource, smoothInverse := hes }
  exact ⟨Φ, him, hGH, hGF, hGH.image_eq.trans (riemannMappingClosedExtension_closed_image hΦ.toLipschitz),
    (hGH.mono sphere_subset_closedBall).image_eq.trans (riemannMappingClosedExtension_sphere_image hΦ.toLipschitz)⟩

/-- Actual disk coordinates on every bounded smooth simply connected domain. -/
theorem exists_smoothConformal_coordinates (Ω : Set ℂ) (hb : Bornology.IsBounded Ω)
    (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω) : ∃ Φ : DiskCoordinates, Φ.domain = Ω := by
  obtain ⟨F, hf, hi, he⟩ := exists_interior_conformal_map Ω hS.1.1 hb hsc
  obtain ⟨Φ, h, _⟩ := (show SmoothUniformization Ω F from ⟨⟨hf, hi, he⟩, hb, hS⟩).coordinates
  exact ⟨Φ, h⟩

end PolyaNeumann
end
