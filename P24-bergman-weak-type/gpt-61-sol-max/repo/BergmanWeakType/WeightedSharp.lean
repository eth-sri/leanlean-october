/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Weighted.WeightedPotential
import BergmanWeakType.Weighted.RadialLevel
import BergmanWeakType.Weighted.RadialKernel
import BergmanWeakType.Weighted.PolarIntegral
import BergmanWeakType.WeakType
import Mathlib.Tactic

variable {α : ℝ}

/-! # Sharp positive weighted constants and the complex weighted upper bound -/




open MeasureTheory Real
open scoped Topology

namespace BergmanWeakType



/-- A radius whose exterior weighted disk has measure `y`. -/
noncomputable def massRadius (α y : ℝ) : ℝ := sqrt (1 - y ^ (α + 1)⁻¹)

theorem massRadius_mem_unit {y : ℝ} (hp : 0 < α + 1) (hy : y ∈ unitIoo) :
    massRadius α y ∈ unitIoo := by
  constructor
  · exact sqrt_pos.mpr (sub_pos.mpr (rpow_lt_one hy.1.le hy.2 (inv_pos.mpr hp)))
  · exact (sqrt_lt' zero_lt_one).mpr
      (by simpa using sub_lt_self 1 (rpow_pos_of_pos hy.1 _))



abbrev outerAnnulus (t : ℝ) : Set ℂ := {w | t < ‖w‖}

open Weighted

/-- The sharp positive weighted weak type bound for every admissible standard weight. -/
theorem isWeakTypeBound_weightedPositiveProjection  (hα : -1 < α) :
    IsWeakTypeBound (weightedArea α) (weightedPositiveProjection α)
      (ENNReal.ofReal (gammaConstant α)) := by
  intro f hf t ht
  let s := t / gammaConstant α
  have hD := gammaConstant_pos hα
  have hs := div_pos ht hD
  have hp := neg_lt_iff_pos_add.mp hα
  have hr {y} (hy : y ∈ unitIoo) := Set.Ioo_subset_Ico_self (massRadius_mem_unit hp hy)
  have hi := integral_mul_radialLevelFraction_le (ρ := massRadius α) (measurable_weightedNormalizedPotential hf)
    (fun z ↦ div_nonneg
      (integral_nonneg fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (normalizer_nonneg α _)) (by unfold massRadius; fun_prop)
    (by
      intro c y hy u hu hyu
      exact antitoneOn_circleAverage_min_weightedNormalizedPotential hf c
        (hr hu)
        (hr hy)
        (by
          apply sqrt_le_sqrt
          exact sub_le_sub_left (rpow_le_rpow hy.1.le hyu (inv_nonneg.mpr (by linarith))) 1))
    (by
      intro y hy c
      have h := antitoneOn_circleAverage_min_weightedNormalizedPotential hf c
        (by simp) (hr hy) (hr hy).1
      simp_all [radialCapMean, weightedNormalizedPotential, weightedPotential,
        weightedKernel, normalizer, boundaryMoment]
      exact h.1) hs.le
  rw [intervalIntegral.integral_const_mul] at hi
  let S := disk ∩ {z : ℂ | s * (1 - ‖z‖ ^ 2) ^ (α + 1) < weightedNormalizedPotential α f z}
  conv_lhs at hi =>
    arg 2
    equals (weightedArea α).real S =>
      have hS : MeasurableSet S := measurableSet_disk.inter (measurableSet_lt (by fun_prop) (measurable_weightedNormalizedPotential hf))
      trans ∫ y in 0..1, circleAverage (S.indicator (fun _ ↦ 1)) 0 (massRadius α y)
      · simp only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro y hy
        apply circleAverage_congr_sphere
        intro z hz
        have hr := massRadius_mem_unit hp hy
        have hn := by simpa [abs_of_pos hr.1] using hz
        have hpow : (1 - ‖z‖ ^ 2) ^ (α + 1) = y := by
          rw [hn, massRadius, sq_sqrt (sub_nonneg.mpr (rpow_lt_one hy.1.le hy.2 (inv_pos.mpr hp)).le), sub_sub_cancel, rpow_inv_rpow hy.1.le hp.ne']
        simp [S, s, ((mem_disk_iff z).mpr (hn.trans_lt hr.2)), hpow, Set.indicator]
      · rw [← integral_indicator_one hS]
        symm
        rw [integral_weightedArea_eq_diskArea hα,
          integral_diskArea_eq_circleAverage_sqrt_one_sub (integrable_weightedDensity_smul hα ((integrable_const 1).indicator hS))]
        simp only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
        rw [integral_unit_interval_rpow hp (fun y ↦ circleAverage (S.indicator (fun _ ↦ (1 : ℝ))) 0 _)]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro y hy
        have hrad : massRadius α (y ^ (α + 1)) = sqrt (1 - y) := by
          grind [BergmanWeakType.massRadius, Real.rpow_rpow_inv]
        dsimp only [radialDensity]
        rw [hrad, add_sub_cancel_right, ← circleAverage_fun_smul]
        apply circleAverage_congr_sphere
        intro z hz
        have hn : ‖z‖ = sqrt (1 - y) := by
          simp_all
        dsimp only
        rw [hn, sq_sqrt (sub_nonneg.mpr hy.2.le), sub_sub_cancel]
        rfl
  have hm : weightedArea α {z | ENNReal.ofReal t < weightedPositiveProjection α f z} ≤
      weightedArea α S := by
    apply measure_mono_ae
    filter_upwards [ae_mem_disk_weightedArea α] with z hz
    intro hlevel
    refine ⟨hz, ?_⟩
    change s * _ < _
    have hz1 := (mem_disk_iff z).mp hz
    have hbound : (1 - ‖z‖ ^ 2) ^ (α + 1) * normalizer α ‖z‖ ≤ gammaConstant α := by
      rw [radialMass_mul_normalizer α (by simpa using hz1)]
      apply ge_of_tendsto (tendsto_circleAverage_boundaryPower hα)
      filter_upwards [Ioo_mem_nhdsLT hz1] with R hR
      exact circleAverage_boundaryPower_mono α (norm_nonneg z) hR.1.le hR.2
    have hF : t < weightedPotential α f z := by
      have hp := ofReal_integral_norm_eq_lintegral_enorm (integrable_weightedKernel_mul hα hf hz)
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mp
      convert hlevel using 1
      simpa only [weightedPotential, weightedPositiveProjection, norm_mul, enorm_mul, ofReal_norm]
        using hp
    rw [weightedNormalizedPotential, lt_div_iff₀ (normalizer_pos (by simp_all))]
    have hscale := mul_le_mul_of_nonneg_left hbound (div_nonneg ht.le hD.le)
    have hcancel  := div_mul_cancel₀ t hD.ne'
    linarith
  have hreal  := by
    have hsmall := (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _) hm) hs.le).trans hi
    exact ((div_le_iff₀ hD).mp (by
      simpa only [s, div_mul_eq_mul_div] using! hsmall)).trans_eq (mul_comm _ _)
  simpa [ENNReal.ofReal_mul ht.le, measureReal_def, ENNReal.ofReal_toReal _, ENNReal.ofReal_mul hD.le, ofReal_integral_norm_eq_lintegral_enorm hf] using ENNReal.ofReal_le_ofReal hreal

theorem weightedPositiveProjection_constant_eq (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (weightedPositiveProjection α) =
      ENNReal.ofReal (gammaConstant α) := by
  let μ := weightedArea α
  refine le_antisymm (sInf_le (isWeakTypeBound_weightedPositiveProjection hα)) ?_
  apply le_sInf
  intro C hC
  have hlim := ENNReal.tendsto_ofReal
    (tendsto_circleAverage_boundaryPower hα)
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with R ⟨hR, hR1⟩
  simp
  rw [← radialMass_mul_normalizer α (by grind)]
  have hnormal := ((continuousOn_normalizer α).continuousAt
    (Ico_mem_nhds_iff.mpr ⟨hR, hR1⟩)).tendsto.comp
      (by simpa only [id_eq, one_mul] using!
          (((continuousAt_id (x := 1)).mul_const R).tendsto.mono_left
            (nhdsWithin_le_nhds (s := Set.Iio 1))))
  have hR := hR.le
  have hlim := ENNReal.tendsto_ofReal
    (hnormal.const_mul ((1 - R ^ 2) ^ (α + 1)))
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ⟨ht, ht1⟩
  have ht := ht.le
  let ℓ := normalizer α (t * R)
  change ENNReal.ofReal ((1 - R ^ 2) ^ (α + 1) * ℓ) ≤ C
  rw [mul_comm]
  have hℓ : 0 < ℓ := normalizer_pos (by simp_all [abs_of_nonneg] <;> nlinarith)
  let s := outerAnnulus t
  let f : ℂ → ℂ := s.indicator (fun _ ↦ 1)
  let m := μ.real s
  have hs : MeasurableSet s := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hspos : 0 < μ s := by
    rw [weightedArea_norm_gt hα ht ht1]
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by nlinarith) _)
  have hsub : ∀ᵐ z ∂μ, z ∈ outerAnnulus R →
      ENNReal.ofReal (ℓ * m) ≤ weightedPositiveProjection α f z := by
    filter_upwards [ae_mem_disk_weightedArea α] with z hzd hz
    have hN : Integrable (fun w : ℂ ↦ normalizer α (‖w‖ * ‖z‖)) μ := by
      apply (integrable_const _).mono'
        (by apply Measurable.aestronglyMeasurable; fun_prop)
      filter_upwards [ae_mem_disk_weightedArea α] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (normalizer_nonneg α _)]
      exact circleAverage_boundaryPower_mono _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_le_of_le_one_left (norm_nonneg z) ((mem_disk_iff w).mp hw).le)
        ((mem_disk_iff z).mp hzd)
    have hlo : ℓ * m ≤ ∫ w in s, ‖weightedKernel α z w‖ ∂μ := by
      conv_rhs =>
        equals ∫ w in s, normalizer α (‖w‖ * ‖z‖) ∂μ =>
          have hK := by simpa only [mul_one] using (integrable_weightedKernel_mul hα (integrable_const 1) hzd).norm
          rw [← integral_indicator hs, ← integral_indicator hs,
            integral_weightedArea_eq_circleAverage hα (hK.indicator hs),
            integral_weightedArea_eq_circleAverage hα
              (hN.indicator hs)]
          apply setIntegral_congr_fun measurableSet_Ioo
          intro r hr
          dsimp only
          congr 1
          have hc := circleAverage_weightedKernel_norm α z hr.1.le
          by_cases ht : t < r <;>
            simp [Real.circleAverage_def, Set.indicator, s, outerAnnulus, ht, abs_of_pos hr.1] at hc ⊢
          field_simp at hc
          simpa only [mul_comm Real.pi] using hc
      calc
        ℓ * m = ∫ _w in s, ℓ ∂μ := by simp [m, mul_comm]
        _ ≤ _ := by
          apply integral_mono_ae (integrable_const _) hN.integrableOn
          filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae (ae_mem_disk_weightedArea α)] with w hw hwd
          apply circleAverage_boundaryPower_mono _ (mul_nonneg ht hR)
          · exact mul_le_mul hw.le hz.le hR (norm_nonneg w)
          · exact (mul_le_of_le_one_left (norm_nonneg z) ((mem_disk_iff w).mp hwd).le).trans_lt ((mem_disk_iff z).mp hzd)
    refine (ENNReal.ofReal_le_ofReal hlo).trans ?_
    simpa only [enorm_norm, weightedPositiveProjection, f, ← lintegral_indicator hs,
      Set.indicator, apply_ite, enorm_one, enorm_zero, mul_ite, mul_one, mul_zero, ofReal_norm] using ((Real.ofReal_le_enorm _).trans (enorm_integral_le_lintegral_enorm
      (μ := μ.restrict s) (fun w ↦ ‖weightedKernel α z w‖)))

  have h := hC.le_of_indicator hs hspos.ne' hℓ hsub
  rwa [show μ _ = _ from weightedArea_norm_gt hα hR hR1,
    ← ENNReal.ofReal_mul hℓ.le] at h

theorem weightedProjection_constant_le (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) ≤
      ENNReal.ofReal (gammaConstant α) := by
  apply sInf_le
  intro f hf t ht
  refine (mul_le_mul_right (measure_mono ?_) _).trans
    (isWeakTypeBound_weightedPositiveProjection hα f hf t ht)
  intro z hz
  change ENNReal.ofReal t < _
  apply hz.trans_le
  simpa only [weightedProjection, weightedPositiveProjection, enorm_mul, ofReal_norm] using
    enorm_integral_le_lintegral_enorm (fun w ↦ weightedKernel α z w * f w)

end BergmanWeakType
