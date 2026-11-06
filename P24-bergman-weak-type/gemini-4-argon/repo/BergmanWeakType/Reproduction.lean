/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Interior kernel columns and the universal lower bound one -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace BergmanWeakType

/-- Every interior kernel column satisfies the weak bound of the complex projection. -/
theorem column_le_weakBound {α L : ℝ} {C : ℝ≥0∞} (hα : -1 < α)
    (hC : IsWeakTypeBound (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) C)
    {a : ℂ} (ha : a ∈ disk) {E : Set ℂ} (hE : E ⊆ disk)
    (hcol : ∀ z ∈ E, L ≤ ‖weightedKernel α z a‖) (hL : 0 < L) :
    ENNReal.ofReal L * weightedArea α E ≤ C := by
  let := weightedArea_isProbabilityMeasure α hα
  have hlim : Filter.Tendsto (fun ℓ : ℝ ↦ ENNReal.ofReal ℓ * weightedArea α E)
      (𝓝[<] L) (𝓝 (ENNReal.ofReal L * weightedArea α E)) :=
    ((ENNReal.continuous_mul_const (measure_ne_top (weightedArea α) E)).comp
      ENNReal.continuous_ofReal).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hL] with ℓ ⟨hℓ, hℓL⟩
  let R := (1 + ‖a‖) / 2
  have ha' : ‖a‖ < 1 := (mem_disk_iff a).mp ha
  have haR : ‖a‖ < R := by dsimp [R]; linarith
  have hcont : ContinuousOn (fun u : ℂ ↦ (1 - u) ^ (-(α + 2) : ℂ)) (Metric.closedBall 0 R) :=
    (continuous_const.sub continuous_id).continuousOn.cpow_const fun u hu ↦ by
      have hu' : ‖u‖ ≤ R := by simpa using hu
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (by
        change 0 < 1 - u.re; dsimp [R] at hu'; linarith [Complex.re_le_norm u]))
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall (0 : ℂ) R).uniformContinuousOn_of_continuous hcont)
    ((L - ℓ) / 2) (by linarith)
  let r := min δ (R - ‖a‖)
  have hr : 0 < r := lt_min hδ (sub_pos.mpr haR)
  have hr1 : r ≤ 1 - ‖a‖ := (min_le_right _ _).trans (by dsimp [R]; linarith)
  let s := Metric.ball a r
  let f : ℂ → ℂ := s.indicator (fun _ ↦ 1)
  let m := (weightedArea α).real s
  have hs : MeasurableSet s := Metric.isOpen_ball.measurableSet
  have hsub_disk : s ⊆ disk := fun w hw ↦ (mem_disk_iff w).mpr <| by
    have hw' : ‖w - a‖ < r := by simpa only [s, Metric.mem_ball, dist_eq_norm] using hw
    have htri := norm_add_le (w - a) a
    rw [sub_add_cancel] at htri; linarith
  have hspos : 0 < weightedArea α s := pos_iff_ne_zero.mpr fun h ↦ by
    have hd := diskArea_absolutelyContinuous_weightedArea α hα h
    rw [diskArea, Measure.restrict_eq_self _ hsub_disk, area_ball] at hd
    exact (by positivity : 0 < ENNReal.ofReal r ^ 2).ne' hd
  have hsfinite : weightedArea α s ≠ ∞ := measure_ne_top _ _
  have hm : 0 < m := ENNReal.toReal_pos hspos.ne' hsfinite
  have hf : Integrable f (weightedArea α) := (integrable_const (1 : ℂ)).indicator hs
  have hmass : (∫⁻ w, ‖f w‖ₑ ∂weightedArea α) = weightedArea α s := by
    simp [f, enorm_indicator_eq_indicator_enorm, hs]
  have hsub : E ⊆ {z | ENNReal.ofReal (ℓ * m) < ‖weightedProjection α f z‖ₑ} := by
    intro z hz
    have hzd : z ∈ disk := hE hz
    have hz' : ‖z‖ ≤ 1 := ((mem_disk_iff z).mp hzd).le
    have hK : Integrable (weightedKernel α z) (weightedArea α) := by
      simpa only [mul_one] using integrable_weightedKernel_mul hα (integrable_const (1 : ℂ)) hzd
    have hset : weightedProjection α f z = ∫ w in s, weightedKernel α z w ∂weightedArea α := by
      rw [weightedProjection, ← integral_indicator hs]
      exact integral_congr_ae (Filter.Eventually.of_forall fun w ↦ by by_cases hw : w ∈ s <;> simp [f, hw])
    have herr : ‖weightedProjection α f z - (m : ℂ) * weightedKernel α z a‖ ≤ (L - ℓ) / 2 * m := by
      rw [hset, ← Complex.real_smul, ← setIntegral_const, ← integral_sub hK.integrableOn (integrable_const _)]
      refine norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun w hw ↦ ?_
      have hw' : ‖w - a‖ < r := by simpa only [s, Metric.mem_ball, dist_eq_norm] using hw
      have hwR : ‖w‖ ≤ R := by
        have htri := norm_add_le (w - a) a
        rw [sub_add_cancel] at htri
        linarith [hw'.trans_le (min_le_right _ _)]
      have hza : z * star a ∈ Metric.closedBall 0 R := by
        simp only [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg a) hz').trans haR.le
      have hzw : z * star w ∈ Metric.closedBall 0 R := by
        simp only [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg w) hz').trans hwR
      have hdist : dist (z * star w) (z * star a) < δ := by
        rw [dist_eq_norm, ← mul_sub, ← star_sub, norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _) hz').trans_lt (hw'.trans_le (min_le_left _ _))
      simpa only [weightedKernel, dist_eq_norm] using (hclose _ hzw _ hza hdist).le
    have hrev : m * ‖weightedKernel α z a‖ - ‖weightedProjection α f z‖ ≤
        ‖weightedProjection α f z - (m : ℂ) * weightedKernel α z a‖ := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm, norm_sub_rev]
        using norm_sub_norm_le ((m : ℂ) * weightedKernel α z a) (weightedProjection α f z)
    have hout : ℓ * m < ‖weightedProjection α f z‖ := by
      nlinarith [mul_le_mul_of_nonneg_left (hcol z hz) hm.le]
    change ENNReal.ofReal (ℓ * m) < ‖weightedProjection α f z‖ₑ
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff ((mul_pos hℓ hm).trans hout)).mpr hout
  have hb : ENNReal.ofReal (ℓ * m) * weightedArea α E ≤ C * weightedArea α s :=
    (mul_le_mul_right (measure_mono hsub) _).trans (by simpa only [hmass] using hC f hf (ℓ * m) (mul_pos hℓ hm))
  rw [ENNReal.ofReal_mul hℓ.le, show ENNReal.ofReal m = weightedArea α s from ENNReal.ofReal_toReal hsfinite,
    mul_assoc, mul_comm (weightedArea α s), ← mul_assoc] at hb
  exact (ENNReal.mul_le_mul_iff_left hspos.ne' hsfinite).mp hb

/-- Interior concentration gives the universal complex weighted lower bound. -/
theorem one_le_weightedProjection_constant (α : ℝ) (hα : -1 < α) :
    1 ≤ weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  let := weightedArea_isProbabilityMeasure α hα
  apply le_sInf
  intro C hC
  have h := column_le_weakBound hα hC (show (0 : ℂ) ∈ disk by simp [disk]) Set.Subset.rfl
    (fun z _ ↦ by simp [weightedKernel]) zero_lt_one
  have hd : weightedArea α disk = 1 := by
    rw [← measure_univ (μ := weightedArea α)]
    exact measure_congr (Filter.eventuallyEqSet_univ.mpr (ae_mem_disk_weightedArea α))
  simpa [hd] using h

theorem one_le_projection_constant :
    1 ≤ weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) := by
  have h := one_le_weightedProjection_constant 0 (by norm_num)
  rwa [weightedArea_zero, show (fun f z ↦ ‖weightedProjection 0 f z‖ₑ) =
    (fun f z ↦ ‖projection f z‖ₑ) by ext f z; simp [weightedProjection, projection]] at h

end BergmanWeakType
