/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.PolarPotential
public import BergmanWeakType.Weighted.QuotientCap
public import BergmanWeakType.Weighted.NormalizerRadial
public import BergmanWeakType.KernelIntegrability

/-! # Weighted positive potentials and their normalized circular caps -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped Topology ENNReal

namespace BergmanWeakType.Weighted

def weightedPotential (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  ∫ w, ‖weightedKernel α z w‖ * ‖f w‖ ∂weightedArea α

def weightedNormalizedPotential (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  weightedPotential α f z / normalizer α ‖z‖

def weightedDiskPotential (α : ℝ) (f : ℂ → ℂ) : ℂ → ℝ :=
  disk.indicator (weightedNormalizedPotential α f)

theorem weightedDiskPotential_nonneg (α : ℝ) (f : ℂ → ℂ) (z : ℂ) :
    0 ≤ weightedDiskPotential α f z :=
  indicator_nonneg (fun w _ ↦ div_nonneg
    (integral_nonneg fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (normalizer_nonneg α ‖w‖)) z

theorem weightedDiskPotential_eq {α : ℝ} {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ disk) :
    weightedDiskPotential α f z = weightedNormalizedPotential α f z :=
  indicator_of_mem hz _

theorem weightedPotential_eq_toReal {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : Integrable f (weightedArea α)) {z : ℂ} (hz : z ∈ disk) :
    weightedPotential α f z = (weightedPositiveProjection α f z).toReal := by
  rw [weightedPotential, weightedPositiveProjection]
  simp only [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun w ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  simpa only [norm_mul] using (integrable_weightedKernel_mul hα hf hz).norm.aestronglyMeasurable

theorem ae_mem_weighted_closedDisk (α : ℝ) :
    ∀ᵐ w ∂weightedArea α, w ∈ Metric.closedBall 0 1 :=
  (ae_mem_disk_weightedArea α).mono fun _ hw ↦ Metric.ball_subset_closedBall hw

theorem measurable_weightedDiskPotential {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : Integrable f (weightedArea α)) : Measurable (weightedDiskPotential α f) := by
  classical
  refine ContinuousOn.measurable_piecewise (f := weightedNormalizedPotential α f)
    (s := disk) ?_ continuousOn_const measurableSet_disk
  apply ContinuousOn.div
  · intro z hz
    have hz' := (mem_disk_iff z).mp hz
    have hR : (‖z‖ + 1) / 2 < 1 := by linarith
    have hzR : z ∈ Metric.ball 0 ((‖z‖ + 1) / 2) := by
      simp only [Metric.mem_ball, dist_zero_right]
      linarith
    exact ((continuousOn_integral_mul_of_compact (isCompact_closedBall 0 1)
      (ae_mem_weighted_closedDisk α) (isCompact_closedBall 0 ((‖z‖ + 1) / 2)) hf.norm (by
        simp_rw [norm_weightedKernel]
        apply ((continuous_const.sub (continuous_fst.mul
          (continuous_star.comp continuous_snd))).norm.continuousOn).rpow_const
        exact fun p hp ↦ .inl (norm_ne_zero_iff.mpr
          (kernel_denominator_ne_zero_closed_input hR hp.1 hp.2)))).continuousAt
      (Metric.closedBall_mem_nhds_of_mem hzR)).continuousWithinAt
  · exact (continuousOn_normalizer α).comp continuous_norm.continuousOn fun z hz ↦
      ⟨norm_nonneg z, (mem_disk_iff z).mp hz⟩
  · exact fun z hz ↦ (normalizer_pos hα
      (by simpa only [abs_norm] using (mem_disk_iff z).mp hz)).ne'

theorem weightedPotential_circleMap (α : ℝ) (f : ℂ → ℂ) (r θ : ℝ) :
    weightedPotential α f (circleMap 0 r θ) =
      polarIntegral (polarKernel (-(α + 2) / 2)) Complex.re Complex.im
        (weightedArea α) (fun w ↦ ‖f w‖) r θ := by
  simp only [weightedPotential, polarIntegral, polarKernel_eq_norm_weightedKernel]

theorem antitoneOn_angularMean_normalized_polarIntegral
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {K : Set X} {a b : X → ℝ} {μ : Measure X} {f : X → ℝ}
    (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) (hf : Integrable f μ)
    (ha : ContinuousOn a K) (hb : ContinuousOn b K)
    (hsource : ∀ w ∈ K, a w ^ 2 + b w ^ 2 ≤ 1) (hfn : ∀ᵐ w ∂μ, 0 ≤ f w)
    {α : ℝ} (hα : -1 < α) (c : ℝ) :
    AntitoneOn (angularMean (fun r θ ↦
      min (polarIntegral (polarKernel (-(α + 2) / 2)) a b μ f r θ / normalizer α r) c))
      (Ico 0 1) := by
  have hr2 (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) : r ^ 2 < 1 :=
    (sq_lt_one_iff_abs_lt_one r).mpr (abs_lt.mpr ⟨by linarith [hr.1], hr.2⟩)
  apply antitoneOn_angularMean_min_quotient (α + 2) c
    (Fr := polarIntegral (polarKernelR (-(α + 2) / 2)) a b μ f)
    (Frr := polarIntegral (polarKernelRR (-(α + 2) / 2)) a b μ f)
    (Ft := polarIntegral (polarKernelT (-(α + 2) / 2)) a b μ f)
    (Ftt := polarIntegral (polarKernelTT (-(α + 2) / 2)) a b μ f)
    (Jr := normalizerFirst α) (Jrr := normalizerSecond α)
  all_goals try exact continuousOn_polarIntegral_unit hK hμ hf (by fun_prop)
  · intro r hr θ
    exact polarIntegral_kernel_hasDerivAt_r hK hμ hf ha hb hsource _ (hr2 r hr) θ
  · intro r hr θ
    exact polarIntegral_kernelR_hasDerivAt_r hK hμ hf ha hb hsource _ (hr2 r hr) θ
  · intro r hr θ
    exact polarIntegral_kernel_hasDerivAt_t hK hμ hf ha hb hsource _ (hr2 r hr) θ
  · intro r hr θ
    exact polarIntegral_kernelT_hasDerivAt_t hK hμ hf ha hb hsource _ (hr2 r hr) θ
  · intro r hr
    simp [polarIntegral, polarKernel, polarDenominator, radialComponent]
  · intro r hr
    simp [polarIntegral, polarKernelT, polarKernel, polarDenominator, radialComponent,
      angularComponent]
  · exact continuousOn_normalizer α
  · apply (continuousOn_polarIntegral_unit isCompact_Icc
      (ae_restrict_mem measurableSet_Icc)
      (integrable_const (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * π))) ((2 * π)⁻¹))
      (by fun_prop (disch := simp [cos_sq_add_sin_sq]))).comp
        (continuous_id.prodMk continuous_const).continuousOn
    exact fun r hr ↦ ⟨hr, Set.mem_univ _⟩
  · apply (continuousOn_polarIntegral_unit isCompact_Icc
      (ae_restrict_mem measurableSet_Icc)
      (integrable_const (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * π))) ((2 * π)⁻¹))
      (by fun_prop (disch := simp [cos_sq_add_sin_sq]))).comp
        (continuous_id.prodMk continuous_const).continuousOn
    exact fun r hr ↦ ⟨hr, Set.mem_univ _⟩
  · intro r hr
    have hd := polarIntegral_kernel_hasDerivAt_r isCompact_Icc
      (ae_restrict_mem measurableSet_Icc)
      (integrable_const (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * π))) ((2 * π)⁻¹))
      continuous_cos.continuousOn continuous_sin.continuousOn
      (fun t _ ↦ (cos_sq_add_sin_sq t).le) (-(α + 2) / 2) (hr2 r hr) 0
    simpa only [polarIntegral_boundary_eq_normalizer, normalizerFirst] using hd
  · intro r hr
    exact polarIntegral_kernelR_hasDerivAt_r isCompact_Icc
      (ae_restrict_mem measurableSet_Icc)
      (integrable_const (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * π))) ((2 * π)⁻¹))
      continuous_cos.continuousOn continuous_sin.continuousOn
      (fun t _ ↦ (cos_sq_add_sin_sq t).le) (-(α + 2) / 2) (hr2 r hr) 0
  · intro r hr
    exact normalizer_pos hα (by simpa only [abs_of_nonneg hr.1] using hr.2)
  · intro r hr
    convert normalizer_ode α (hr2 r hr) hr.1.ne' using 1
    ring
  · intro r hr θ
    convert polarIntegral_operator_nonpos hK hμ hf ha hb hsource (α + 2)
      (hr2 r hr) hr.1.ne' θ hfn using 1
    unfold polarOperator
    ring

/-- Normalizing by the exact circular kernel average makes every capped circular mean
of an admissible weighted potential decrease with radius. -/
theorem antitoneOn_circleAverage_min_weightedNormalizedPotential {α : ℝ} (hα : -1 < α)
    {f : ℂ → ℂ} (hf : Integrable f (weightedArea α)) (c : ℝ) :
    AntitoneOn (fun r ↦ circleAverage (fun z ↦ min (weightedNormalizedPotential α f z) c) 0 r)
      (Ico 0 1) := by
  have h := antitoneOn_angularMean_normalized_polarIntegral
    (isCompact_closedBall (0 : ℂ) 1) (ae_mem_weighted_closedDisk α) hf.norm
    Complex.continuous_re.continuousOn Complex.continuous_im.continuousOn
    (fun w hw ↦ by
      have hnorm : ‖w‖ ≤ 1 := by simpa using hw
      have heq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
        simp only [Complex.sq_norm, Complex.normSq_apply]
        ring
      nlinarith [norm_nonneg w])
    (Filter.Eventually.of_forall fun w ↦ norm_nonneg (f w)) hα c
  intro r hr s hs hrs
  have heq (u : ℝ) (hu : 0 ≤ u) :
      circleAverage (fun z ↦ min (weightedNormalizedPotential α f z) c) 0 u =
      angularMean (fun r θ ↦ min
        (polarIntegral (polarKernel (-(α + 2) / 2)) Complex.re Complex.im
          (weightedArea α) (fun w ↦ ‖f w‖) r θ / normalizer α r) c) u := by
    rw [Real.circleAverage_def, angularMean]
    simp only [weightedNormalizedPotential, norm_circleMap_zero, abs_of_nonneg hu,
      weightedPotential_circleMap, smul_eq_mul]
  dsimp only
  rw [heq r hr.1, heq s hs.1]
  exact h hr hs hrs

theorem circleAverage_min_weightedDiskPotential_eq {α : ℝ} {f : ℂ → ℂ}
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) (c : ℝ) :
    circleAverage (fun z ↦ min (weightedDiskPotential α f z) c) 0 r =
      circleAverage (fun z ↦ min (weightedNormalizedPotential α f z) c) 0 r := by
  apply circleAverage_congr_sphere
  intro z hz
  have hz' : ‖z‖ = r := by
    simpa only [Metric.mem_sphere, dist_zero_right, abs_of_nonneg hr.1] using hz
  dsimp only
  rw [weightedDiskPotential_eq ((mem_disk_iff z).mpr (hz'.trans_lt hr.2))]

theorem antitoneOn_circleAverage_min_weightedDiskPotential {α : ℝ} (hα : -1 < α)
    {f : ℂ → ℂ} (hf : Integrable f (weightedArea α)) (c : ℝ) :
    AntitoneOn (fun r ↦ circleAverage (fun z ↦ min (weightedDiskPotential α f z) c) 0 r)
      (Ico 0 1) := by
  intro r hr s hs hrs
  dsimp only
  rw [circleAverage_min_weightedDiskPotential_eq hr,
    circleAverage_min_weightedDiskPotential_eq hs]
  exact antitoneOn_circleAverage_min_weightedNormalizedPotential hα hf c hr hs hrs

theorem circleAverage_min_weightedDiskPotential_le_mass {α : ℝ} (hα : -1 < α)
    {f : ℂ → ℂ} (hf : Integrable f (weightedArea α)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) (c : ℝ) :
    circleAverage (fun z ↦ min (weightedDiskPotential α f z) c) 0 r ≤
      ∫ w, ‖f w‖ ∂weightedArea α := by
  rw [circleAverage_min_weightedDiskPotential_eq hr]
  have h := antitoneOn_circleAverage_min_weightedNormalizedPotential hα hf c
    (show (0 : ℝ) ∈ Ico 0 1 by simp) hr hr.1
  have hz : weightedNormalizedPotential α f 0 = ∫ w, ‖f w‖ ∂weightedArea α := by
    simp [weightedNormalizedPotential, weightedPotential, weightedKernel]
  simp only [circleAverage_zero, hz] at h
  exact h.trans (min_le_left _ _)

end BergmanWeakType.Weighted
