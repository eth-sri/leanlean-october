/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.KernelIntegrability
import BergmanWeakType.WeakType
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

variable {a : ℂ} {α L : ℝ} {E : Set ℂ}

/-! # Interior kernel columns as limits of admissible inputs -/





open MeasureTheory
open scoped ENNReal Topology

namespace BergmanWeakType



/-- Every interior kernel column satisfies the weak bound of the complex projection. -/
theorem column_le_weakBound (hα : -1 < α) {C : ℝ≥0∞}
    (hC : IsWeakTypeBound (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) C)
     (ha : a ∈ disk)  (hE : E ⊆ disk)
    (hcol : ∀ z ∈ E, L ≤ ‖weightedKernel α z a‖) (hL : 0 < L) :
    ENNReal.ofReal L * weightedArea α E ≤ C := by
  have hlim := ENNReal.Tendsto.mul_const
    (ENNReal.tendsto_ofReal (Filter.tendsto_id'.mpr
      (nhdsWithin_le_nhds (a := L) (s := Set.Iio L))))
    (Or.inr (measure_ne_top (weightedArea α) E))
  dsimp at hlim
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hL] with ℓ ⟨hℓ, hℓL⟩
  let R := (1 - ‖a‖) / 2
  have ha' := (mem_disk_iff a).mp ha
  have hR : 0 < R := by continuity
  have hcont : ContinuousOn (fun p : ℂ × ℂ ↦ weightedKernel α p.1 p.2)
      (Metric.closedBall 0 1 ×ˢ Metric.closedBall a R) := by
    apply ContinuousOn.cpow_const (by fun_prop)
    intro p hp
    refine Complex.mem_slitPlane_iff.mpr (Or.inl (kernel_denominator_re_pos ?_))
    have hn := norm_le_of_mem_closedBall hp.2
    apply mul_lt_one_of_nonneg_of_lt_one_right (by simp_all) (norm_nonneg _)
    grind
  obtain ⟨δ, hδ, hδclose⟩ := Metric.uniformContinuousOn_iff.mp
    (((isCompact_closedBall 0 1).prod (isCompact_closedBall a R)).uniformContinuousOn_of_continuous hcont) ((L - ℓ) / 2) (by linarith)
  let r := min δ R
  have hclose (z ) (hz : z ∈ disk) (w ) (hw : w ∈ Metric.ball a r)  := by
    have hw' := by simpa only [r, Metric.mem_ball, lt_min_iff] using hw
    simpa [dist_eq_norm] using hδclose (z, w)
      ⟨Metric.ball_subset_closedBall hz, hw'.2.le⟩
      (z, a) ⟨Metric.ball_subset_closedBall hz, Metric.mem_closedBall_self hR.le⟩
      (by simpa using hw'.1)
  let s := Metric.ball a r
  let f : ℂ → ℂ := s.indicator (fun _ ↦ 1)
  let m := (weightedArea α).real s
  have hs : MeasurableSet s := Metric.isOpen_ball.measurableSet
  have hspos : 0 < weightedArea α s := by
    apply pos_iff_ne_zero.mpr
    intro h
    have hp : 0 < area (s ∩ disk) :=
      (Metric.isOpen_ball.inter Metric.isOpen_ball).measure_pos area
        ⟨a, Metric.mem_ball_self (lt_min hδ hR), ha⟩
    exact hp.ne' (by simpa [diskArea, Measure.restrict_apply hs] using (diskArea_absolutelyContinuous_weightedArea α hα h))
  have hm : 0 < m := ENNReal.toReal_pos hspos.ne' (measure_ne_top _ _)
  exact hC.le_of_indicator hs hspos.ne' hℓ (Filter.Eventually.of_forall (by
    intro z hz
    have hK := integrable_weightedKernel_mul hα (integrable_const 1) (hE hz)
    simp at hK
    have herr := norm_setIntegral_le_of_norm_le_const (μ := weightedArea α)
      (measure_lt_top _ s) (fun w hw ↦ (hclose z (hE hz) w hw).le)
    have heq : weightedProjection α f z = ∫ w in s, weightedKernel α z w ∂weightedArea α := by
      simp [weightedProjection, f, ← Set.indicator_mul_right, integral_indicator hs]
    rw [integral_sub hK.integrableOn (integrable_const _), setIntegral_const,
      ← heq, Complex.real_smul] at herr
    have hrev := norm_sub_norm_le (m * weightedKernel α z a) (weightedProjection α f z)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm] at hrev
    rw [norm_sub_rev] at hrev
    change ENNReal.ofReal _ ≤ ‖weightedProjection α f z‖ₑ
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_le_mul_of_nonneg_left (hcol z hz) hm.le]
  ))

theorem one_le_weightedProjection_constant (α : ℝ) (hα : -1 < α) :
    1 ≤ weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  let := weightedArea_isProbabilityMeasure α hα
  apply le_sInf
  intro C hC
  simpa [(mem_ae_iff_prob_eq_one measurableSet_disk).mp (ae_mem_disk_weightedArea α)] using column_le_weakBound hα hC (a := 0) 
    (by simp) (Set.Subset.refl disk) (by simp_all) zero_lt_one

def boundaryCap (R : ℝ) : Set ℂ := disk ∩ Metric.ball 1 R

end BergmanWeakType
