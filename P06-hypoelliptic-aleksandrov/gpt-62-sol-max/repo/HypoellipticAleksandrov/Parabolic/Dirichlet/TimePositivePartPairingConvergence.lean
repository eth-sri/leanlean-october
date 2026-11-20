module

import HypoellipticAleksandrov.Analysis.L2Convergence

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimePositivePart

/-!
# Positive-part dual-pairing convergence

This module packages the finite-measure \(L^2\) convergence argument for the
positive-part map and its induced dual pairings.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open HypoellipticAleksandrov.Analysis Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)

private theorem localPositivePart_memLp
    (f : MeasureTheory.Lp (H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ) :
    MemLp (fun t => h10PositivePart hΩ (f t)) (2 : ℝ≥0∞) μ := by
  apply MemLp.of_le (Lp.memLp f)
  · exact (continuous_h10PositivePart hΩ).comp_aestronglyMeasurable
      (Lp.memLp f).aestronglyMeasurable
  · filter_upwards with t
    exact norm_h10PositivePart_le hΩ (f t)

private noncomputable def localPositivePart :
    MeasureTheory.Lp (H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ →
      MeasureTheory.Lp (H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ :=
  fun f => (localPositivePart_memLp hΩ μ f).toLp
    (fun t => h10PositivePart hΩ (f t))

private theorem coeFn_localPositivePart
    (f : MeasureTheory.Lp (H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ) :
    localPositivePart hΩ μ f =ᵐ[μ] fun t => h10PositivePart hΩ (f t) :=
  (localPositivePart_memLp hΩ μ f).coeFn_toLp

private theorem continuous_localPositivePart
    [IsFiniteMeasure μ] : Continuous (localPositivePart hΩ μ) := continuous_L2_of_pointwise (coeFn_localPositivePart hΩ μ)
    (fun _ => continuous_h10PositivePart hΩ) (fun _ => norm_h10PositivePart_le hΩ)

/-- Strong \(L^2\) convergence is preserved by the pointwise positive-part map. -/
theorem tendsto_positivePart_sqNorm_integral_of_sqNorm
    [IsFiniteMeasure μ] (f : ℝ → H10HilbertGraph hΩ)
    (fh : ℝ → ℝ → H10HilbertGraph hΩ)
    (hf : MemLp f (2 : ℝ≥0∞) μ)
    (hfh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (fh h) (2 : ℝ≥0∞) μ)
    (hconv : Tendsto (fun h : ℝ => ∫ t, ‖fh h t - f t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t,
      ‖h10PositivePart hΩ (fh h t) - h10PositivePart hΩ (f t)‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨F, hF, hFe⟩ := exists_tendsto_L2_of_sqNorm hf hfh hconv
  have hP := (continuous_localPositivePart hΩ μ).continuousAt.tendsto.comp hF
  rw [tendsto_iff_norm_sub_tendsto_zero] at hP
  have hsq := hP.pow 2
  rw [zero_pow (by decide : (2 : ℕ) ≠ 0)] at hsq
  refine hsq.congr' ?_
  filter_upwards [hFe] with h hh
  let x := localPositivePart hΩ μ (F h)
  let y := localPositivePart hΩ μ (hf.toLp f)
  change ‖x - y‖ ^ 2 = _
  rw [← Lp.toLp_coeFn (x - y) (Lp.memLp (x - y)), ← integral_sq_eq_norm_toLp_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub x y, coeFn_localPositivePart hΩ μ (F h),
    coeFn_localPositivePart hΩ μ (hf.toLp f), hh, hf.coeFn_toLp] with t hs hx hy h₁ h₂
  simp only [hs, Pi.sub_apply, x, y, hx, hy, h₁, h₂]

/-- Strong \(L^2\) convergence of primal and dual approximations implies
\(L^1\) convergence of their dual pairing after applying the positive-part map
to the primal approximation. -/
theorem tendsto_dualPairing_positivePart_of_sqNorm
    [IsFiniteMeasure μ]
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    (uh : ℝ → ℝ → H10HilbertGraph hΩ) (gh : ℝ → ℝ → H10HilbertGraphDual hΩ)
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (huh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uh h) 2 μ)
    (hgh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (gh h) 2 μ)
    (hU : Tendsto (fun h : ℝ => ∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0))
    (hG : Tendsto (fun h : ℝ => ∫ t, ‖gh h t - g t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t,
      |(gh h t) (h10PositivePart hΩ (uh h t)) -
        (g t) (h10PositivePart hΩ (u t))| ∂μ) (𝓝[>] 0) (𝓝 0) := by
  have hpos {f : ℝ → H10HilbertGraph hΩ} (hf : MemLp f 2 μ) :=
    hf.of_le ((continuous_h10PositivePart hΩ).comp_aestronglyMeasurable hf.aestronglyMeasurable)
      (.of_forall fun _ => norm_h10PositivePart_le hΩ _)
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply, Real.norm_eq_abs] using
    tendsto_integral_norm_bilin_sub_of_sqNorm (ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ))
      hg (hpos hu) hgh (huh.mono fun _ => hpos) hG
      (tendsto_positivePart_sqNorm_integral_of_sqNorm hΩ μ u uh hu huh hU)

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
