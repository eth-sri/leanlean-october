/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.WeightedPotential
public import BergmanWeakType.Weighted.PolarIntegral
public import BergmanWeakType.Reproduction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Sharp positive weighted constants and the complex weighted upper bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace BergmanWeakType

open Weighted

theorem tendsto_circleAverage_boundaryPower {α : ℝ} (hα : -1 < α) :
    Tendsto (fun r : ℝ ↦ Real.circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ α) 0 1)
      (𝓝[<] 1) (𝓝 (gammaConstant α)) := by
  by_cases hα0 : 0 ≤ α
  · have hc : Continuous (fun z : ℂ ↦ ‖1 - z‖ ^ α) :=
      (continuous_const.sub continuous_id).norm.rpow_const fun _ ↦ Or.inr hα0
    have hlim := (Real.Continuous.circleAverage (c := 0) hc).continuousAt.tendsto.mono_left
      (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
    rw [circleAverage_boundary_power hα] at hlim
    refine hlim.congr fun r ↦ ?_
    simpa only [add_zero] using
      Real.circleAverage_eq_circleAverage_zero_one (f := fun z : ℂ ↦ ‖1 - z‖ ^ α) (c := 0) (R := r)
  · let F : ℝ → ℝ → ℝ := fun r θ ↦ circleDenominator r (Real.cos θ) ^ (α / 2)
    have hci : CircleIntegrable (fun ζ : ℂ ↦ ‖1 - ζ‖ ^ α) 0 1 := by
      by_contra hn
      exact (gammaConstant_pos hα).ne' (circleAverage_boundary_power hα ▸ Real.circleAverage.integral_undef hn)
    have hi : IntervalIntegrable (F 1) volume 0 (2 * Real.pi) := by
      change IntervalIntegrable (fun θ ↦ ‖1 - circleMap 0 1 θ‖ ^ α) volume 0 (2 * Real.pi) at hci
      simpa only [F, ← norm_boundaryKernel_circleMap_rpow, Complex.ofReal_one, one_mul] using hci
    have hb : ∀ᶠ r : ℝ in 𝓝[<] 1, r ∈ Set.Ioo (1 / 2 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
    have hae : ∀ᵐ θ : ℝ, θ ∈ Set.uIoc 0 (2 * Real.pi) → 0 < circleDenominator 1 (Real.cos θ) := by
      filter_upwards [show ∀ᵐ θ : ℝ, θ ≠ 2 * Real.pi by rw [ae_iff]; simp] with θ hθ hθmem
      simp only [Set.uIoc_of_le Real.two_pi_pos.le, Set.mem_Ioc] at hθmem
      have hs : 0 < Real.sin (θ / 2) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθmem.1]) (by linarith [lt_of_le_of_ne hθmem.2 hθ])
      have hn : ‖1 - circleMap 0 1 θ‖ = 2 * Real.sin (θ / 2) := by
        rw [circleMap, zero_add, Complex.ofReal_one, one_mul, norm_sub_rev,
          mul_comm (θ : ℂ) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,
          Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hs)]
      rw [← norm_boundaryKernel_circleMap_sq]
      simpa only [Complex.ofReal_one, one_mul, hn] using sq_pos_of_pos (mul_pos (by norm_num) hs)
    have hlim : Tendsto (fun r ↦ ∫ θ in (0 : ℝ)..2 * Real.pi, F r θ)
        (𝓝[<] 1) (𝓝 (∫ θ in (0 : ℝ)..2 * Real.pi, F 1 θ)) := by
      apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun θ ↦ (1 / 2 : ℝ) ^ (α / 2) * F 1 θ)
      · filter_upwards [hb] with r hr
        refine (Continuous.rpow_const (by dsimp [circleDenominator]; fun_prop) fun θ ↦ Or.inl ?_).aestronglyMeasurable
        exact (circleDenominator_pos (by rw [abs_of_pos (by linarith [hr.1])]; exact hr.2)
          ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩).ne'
      · filter_upwards [hb] with r hr
        filter_upwards [hae] with θ hθ hθmem
        have hd := hθ hθmem
        have he : (1 / 2 : ℝ) * circleDenominator 1 (Real.cos θ) ≤ circleDenominator r (Real.cos θ) := by
          unfold circleDenominator
          nlinarith [mul_nonneg (by linarith [hr.1] : 0 ≤ 2 * r - 1) (sub_nonneg.mpr (Real.cos_le_one θ)),
            sq_nonneg (1 - r)]
        dsimp only [F]
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
        simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hd.le] using
          Real.rpow_le_rpow_of_nonpos (mul_pos (by norm_num) hd) he (by linarith)
      · exact hi.const_mul _
      · filter_upwards [hae] with θ hθ hθmem
        exact ((by dsimp [circleDenominator]; fun_prop :
          ContinuousAt (fun r ↦ circleDenominator r (Real.cos θ)) 1).rpow_const
          (Or.inl (hθ hθmem).ne')).tendsto.mono_left nhdsWithin_le_nhds
    have havg := hlim.const_mul (2 * Real.pi)⁻¹
    have heq (r : ℝ) : Real.circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ α) 0 1 =
        (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi, F r θ) := by
      simp only [Real.circleAverage_def, norm_boundaryKernel_circleMap_rpow, smul_eq_mul, F]
    simp_rw [← heq] at havg
    simpa only [Complex.ofReal_one, one_mul, circleAverage_boundary_power hα] using havg

/-- Admissible outer-annulus inputs recover the exact positive weighted lower constant. -/
theorem gammaConstant_le_weightedPositiveProjection_constant (α : ℝ) (hα : -1 < α) :
    ENNReal.ofReal (gammaConstant α) ≤
      weakTypeConstant (weightedArea α) (weightedPositiveProjection α) := by
  let := weightedArea_isProbabilityMeasure α hα
  let outerAnnulus (t : ℝ) : Set ℂ := {w | t < ‖w‖ ∧ ‖w‖ < 1}
  have hmeas (t : ℝ) : MeasurableSet (outerAnnulus t) :=
    (isOpen_lt continuous_const continuous_norm |>.inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have harea {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
      weightedArea α (outerAnnulus r) = ENNReal.ofReal ((1 - r ^ 2) ^ (α + 1)) := by
    have hcongr : weightedArea α (outerAnnulus r) =
        weightedArea α ((fun z : ℂ ↦ ‖z‖ ^ 2) ⁻¹' Set.Ioi (r ^ 2)) := by
      refine measure_congr ((ae_mem_disk_weightedArea α).mono fun z hz ↦ ?_)
      simp only [outerAnnulus, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi,
        (mem_disk_iff z).mp hz, and_true, sq_lt_sq₀ hr (norm_nonneg z)]
    have hr₂ : r ^ 2 < 1 := by nlinarith
    have hm : Measurable (fun u : ℝ ↦ ENNReal.ofReal ((α + 1) * (1 - u) ^ α)) := by fun_prop
    rw [hcongr, weightedArea, withDensity_apply _ (measurableSet_Ioi.preimage (by fun_prop)),
      ← setLIntegral_map measurableSet_Ioi hm (by fun_prop : Measurable (fun z : ℂ ↦ ‖z‖ ^ 2)),
      map_norm_sq_diskArea, Measure.restrict_restrict measurableSet_Ioi,
      show Set.Ioi (r ^ 2) ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc (r ^ 2) 1 by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
        exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, (sq_nonneg r).trans h.1.le, h.2⟩⟩]
    have hf : IntervalIntegrable (fun u : ℝ ↦ (1 - u) ^ α) volume (r ^ 2) 1 := by
      convert! ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 - r ^ 2) hα).comp_sub_left 1).symm using 1 <;> ring
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (r ^ 2) 1)] (fun u : ℝ ↦ (α + 1) * (1 - u) ^ α) :=
      (ae_restrict_mem measurableSet_Ioc).mono fun u hu ↦
        mul_nonneg (by linarith) (Real.rpow_nonneg (sub_nonneg.mpr hu.2) _)
    have hpos : 0 < α + 1 := by linarith
    rw [← ofReal_integral_eq_lintegral_ofReal (hf.const_mul (α + 1)).1 hnonneg,
      ← intervalIntegral.integral_of_le hr₂.le, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ α) 1, sub_self,
      integral_rpow (Or.inl hα), Real.zero_rpow hpos.ne', sub_zero, mul_div_cancel₀ _ hpos.ne']
  have htend : Tendsto (fun r : ℝ ↦ (1 - r ^ 2) ^ (α + 1) * normalizer α r)
      (𝓝[<] 1) (𝓝 (gammaConstant α)) := by
    refine (tendsto_circleAverage_boundaryPower hα).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
    exact (radialMass_mul_normalizer α (by simpa only [abs_of_pos hr.1] using hr.2)).symm
  apply le_sInf
  intro C hC
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp htend)
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with R ⟨hR0, hR1⟩
  have hR : 0 ≤ R := hR0.le
  have hnormal : Tendsto (fun t : ℝ ↦ normalizer α (t * R)) (𝓝[<] 1) (𝓝 (normalizer α R)) := by
    apply ((continuousOn_normalizer α) R ⟨hR, hR1⟩).tendsto.comp
    refine tendsto_nhdsWithin_iff.mpr ⟨by simpa only [id_eq, one_mul] using!
      (continuousAt_id.mul_const R).tendsto.mono_left (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds), ?_⟩
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact ⟨mul_nonneg ht.1.le hR, (mul_le_of_le_one_left hR ht.2.le).trans_lt hR1⟩
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (hnormal.const_mul ((1 - R ^ 2) ^ (α + 1))))
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ⟨ht0, ht1⟩
  have ht : 0 ≤ t := ht0.le
  dsimp only [Function.comp_def]
  rw [mul_comm]
  have htR : |t * R| < 1 := by
    rw [abs_of_nonneg (mul_nonneg ht hR)]
    exact (mul_le_of_le_one_left hR ht1.le).trans_lt hR1
  apply le_of_tendsto ((ENNReal.continuous_ofReal.comp (continuous_id.mul_const _)).continuousAt.tendsto.mono_left
    (show 𝓝[<] (normalizer α (t * R)) ≤ 𝓝 (normalizer α (t * R)) from nhdsWithin_le_nhds))
  filter_upwards [Ioo_mem_nhdsLT (normalizer_pos hα htR)] with ℓ ⟨hℓ, hℓJ⟩
  let s := outerAnnulus t
  let f : ℂ → ℂ := s.indicator (fun _ ↦ 1)
  let m := (weightedArea α).real s
  have hs : MeasurableSet s := hmeas t
  have hspos : 0 < weightedArea α s := by
    rw [harea ht ht1]
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by nlinarith) _)
  have hsfinite : weightedArea α s ≠ ∞ := measure_ne_top _ _
  have hm : 0 < m := ENNReal.toReal_pos hspos.ne' hsfinite
  have hf : Integrable f (weightedArea α) := (integrable_const (1 : ℂ)).indicator hs
  have hmass : (∫⁻ w, ‖f w‖ₑ ∂weightedArea α) = weightedArea α s := by
    simp [f, enorm_indicator_eq_indicator_enorm, hs]
  have hsub : outerAnnulus R ⊆ {z | ENNReal.ofReal (ℓ * m) < weightedPositiveProjection α f z} := by
    intro z hz
    have hzd : z ∈ disk := (mem_disk_iff z).mpr hz.2
    have hK : Integrable (fun w ↦ ‖weightedKernel α z w‖) (weightedArea α) := by
      simpa only [mul_one] using (integrable_weightedKernel_mul hα (integrable_const (1 : ℂ)) hzd).norm
    have hrad : Integrable (fun w : ℂ ↦ normalizer α (‖w‖ * ‖z‖)) (weightedArea α) := by
      have hm_rad : AEStronglyMeasurable (fun w : ℂ ↦ normalizer α (‖w‖ * ‖z‖)) (weightedArea α) :=
        (((continuousOn_normalizer α).comp (by fun_prop) fun w hw ↦
          ⟨mul_nonneg (norm_nonneg _) (norm_nonneg _),
            (mul_le_of_le_one_left (norm_nonneg z) ((mem_disk_iff w).mp hw).le).trans_lt ((mem_disk_iff z).mp hzd)⟩).aestronglyMeasurable
          (μ := area) measurableSet_disk).mono_ac (withDensity_absolutelyContinuous diskArea _)
      refine (integrable_const (normalizer α ‖z‖)).mono' hm_rad ?_
      filter_upwards [ae_mem_disk_weightedArea α] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (normalizer_nonneg α _)]
      exact normalizer_mono α (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_le_of_le_one_left (norm_nonneg z) ((mem_disk_iff w).mp hw).le) ((mem_disk_iff z).mp hzd)
    have hproj : weightedPositiveProjection α f z =
        ENNReal.ofReal (∫ w in s, ‖weightedKernel α z w‖ ∂weightedArea α) := by
      rw [ofReal_integral_eq_lintegral_ofReal hK.integrableOn (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _),
        weightedPositiveProjection, ← lintegral_indicator hs]
      exact lintegral_congr fun w ↦ by by_cases hw : w ∈ s <;> simp [f, hw, ← ofReal_norm]
    have hint_eq : (∫ w in s, ‖weightedKernel α z w‖ ∂weightedArea α) =
        ∫ w in s, normalizer α (‖w‖ * ‖z‖) ∂weightedArea α := by
      rw [← integral_indicator hs, ← integral_indicator hs,
        integral_weightedArea_eq_circleAverage hα (hK.indicator hs),
        integral_weightedArea_eq_circleAverage hα (hrad.indicator hs)]
      refine setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
      congr 1
      by_cases htr : t < r
      · have hleft : Real.circleAverage (s.indicator (fun w ↦ ‖weightedKernel α z w‖)) 0 r =
            Real.circleAverage (fun w ↦ ‖weightedKernel α z w‖) 0 r :=
          Real.circleAverage_congr_sphere fun w hw ↦ by
            have hw' : ‖w‖ = r := by simpa [abs_of_pos hr.1] using hw
            exact Set.indicator_of_mem (show w ∈ s from ⟨hw' ▸ htr, hw' ▸ hr.2⟩) _
        have hright : Real.circleAverage (s.indicator (fun w ↦ normalizer α (‖w‖ * ‖z‖))) 0 r =
            normalizer α (r * ‖z‖) :=
          Real.circleAverage_const_on_circle fun w hw ↦ by
            have hw' : ‖w‖ = r := by simpa [abs_of_pos hr.1] using hw
            rw [Set.indicator_of_mem (show w ∈ s from ⟨hw' ▸ htr, hw' ▸ hr.2⟩), hw']
        rw [hleft, hright, circleAverage_weightedKernel_norm α z hr.1.le]
      · have heq (g : ℂ → ℝ) : Real.circleAverage (s.indicator g) 0 r = 0 :=
          Real.circleAverage_const_on_circle fun w hw ↦ by
            have hw' : ‖w‖ = r := by simpa [abs_of_pos hr.1] using hw
            exact Set.indicator_of_notMem (by simpa only [s, outerAnnulus, Set.mem_ofPred_eq, hw', hr.2, and_true] using htr) _
        rw [heq, heq]
    have hout : ℓ * m < ∫ w in s, ‖weightedKernel α z w‖ ∂weightedArea α := by
      refine (mul_lt_mul_of_pos_right hℓJ hm).trans_le ?_
      rw [hint_eq, show normalizer α (t * R) * m = ∫ _ in s, normalizer α (t * R) ∂weightedArea α by simp [m, mul_comm]]
      refine integral_mono_ae (integrable_const _) hrad.integrableOn ?_
      filter_upwards [ae_restrict_mem hs] with w hw
      exact normalizer_mono α (mul_nonneg ht hR) (mul_le_mul hw.1.le hz.1.le hR (norm_nonneg w))
        ((mul_le_of_le_one_left (norm_nonneg z) hw.2.le).trans_lt ((mem_disk_iff z).mp hzd))
    change ENNReal.ofReal (ℓ * m) < weightedPositiveProjection α f z
    rw [hproj]
    exact (ENNReal.ofReal_lt_ofReal_iff ((mul_pos hℓ hm).trans hout)).mpr hout
  have hbound : ENNReal.ofReal (ℓ * m) * weightedArea α (outerAnnulus R) ≤ C * weightedArea α s :=
    (mul_le_mul_right (measure_mono hsub) _).trans (by simpa only [hmass] using hC f hf (ℓ * m) (mul_pos hℓ hm))
  rw [harea hR hR1, ENNReal.ofReal_mul hℓ.le,
    show ENNReal.ofReal m = weightedArea α s from ENNReal.ofReal_toReal hsfinite,
    mul_assoc, mul_comm (weightedArea α s), ← mul_assoc] at hbound
  simpa only [Function.comp_def, id_eq, ENNReal.ofReal_mul hℓ.le] using
    (ENNReal.mul_le_mul_iff_left hspos.ne' hsfinite).mp hbound

abbrev radialCapMean (U : ℂ → ℝ) (ρ : ℝ → ℝ) (y c : ℝ) : ℝ :=
  circleAverage (fun z ↦ min (U z) c) 0 (ρ y)

abbrev radialLevelFraction (U : ℂ → ℝ) (ρ : ℝ → ℝ) (t y : ℝ) : ℝ :=
  circleAverage (fun z ↦ if t * y < U z then (1 : ℝ) else 0) 0 (ρ y)

/-- Increasing cap means in the mass coordinate give the integrated level-set estimate. -/
theorem integral_mul_radialLevelFraction_le {U : ℂ → ℝ} (hU : Measurable U)
    (hUpos : ∀ z, 0 ≤ U z) {ρ : ℝ → ℝ} (hρ : Measurable ρ) {M : ℝ}
    (hmono : ∀ c, MonotoneOn (fun y ↦ radialCapMean U ρ y c) (Ioo 0 1))
    (hbound : ∀ y ∈ Ioo (0 : ℝ) 1, ∀ c, radialCapMean U ρ y c ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ y in (0 : ℝ)..1, t * radialLevelFraction U ρ t y) ≤ M := by
  have hci_bdd {g : ℂ → ℝ} (hg : Measurable g) {B : ℝ} (hb : ∀ z, ‖g z‖ ≤ B) (r : ℝ) :
      CircleIntegrable g 0 r := by
    rw [CircleIntegrable, intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le]
    exact Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
      (hg.comp (continuous_circleMap 0 r).measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ ↦ hb _)
  have hint_comp {F : ℝ → ℂ → ℝ} {B : ℝ}
      (hF : Measurable fun p : ℝ × ℝ ↦ F p.1 (circleMap 0 (ρ p.1) p.2))
      (hb : ∀ y ∈ Icc (0 : ℝ) 1, ‖circleAverage (F y) 0 (ρ y)‖ ≤ B) :
      IntegrableOn (fun y ↦ circleAverage (F y) 0 (ρ y)) (Icc (0 : ℝ) 1) := by
    have hi := hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) (2 * π)))
    have hm : Measurable fun y ↦ circleAverage (F y) 0 (ρ y) := by
      simp only [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le]
      exact measurable_const.mul hi.measurable
    exact Measure.integrableOn_of_bounded measure_Icc_lt_top.ne hm.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Icc).mono hb)
  have hpoint : Measurable fun p : ℝ × ℝ ↦ circleMap 0 (ρ p.1) p.2 :=
    circleMap.continuous.measurable.comp ((hρ.comp measurable_fst).prodMk measurable_snd)
  have hci_lev (y r : ℝ) : CircleIntegrable (fun z ↦ if t * y < U z then (1 : ℝ) else 0) 0 r :=
    hci_bdd (B := 1) (measurable_const.ite (measurableSet_lt measurable_const hU) measurable_const)
      (fun _ ↦ by split_ifs <;> norm_num) r
  have hci_cap (c r : ℝ) : CircleIntegrable (fun z ↦ min (U z) c) 0 r :=
    hci_bdd (hU.inf measurable_const)
      (fun z ↦ by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨le_min ((neg_nonpos.mpr (abs_nonneg c)).trans (hUpos z)) (neg_abs_le c),
          (min_le_right _ _).trans (le_abs_self c)⟩) r
  have hlev_int : IntegrableOn (radialLevelFraction U ρ t) (Icc (0 : ℝ) 1) :=
    hint_comp (B := 1) (measurable_const.ite (measurableSet_lt (measurable_const.mul measurable_fst)
      (hU.comp hpoint)) measurable_const) fun y _ ↦ by
      rw [Real.norm_of_nonneg (circleAverage_nonneg_of_nonneg fun _ _ ↦ by split_ifs <;> norm_num)]
      exact circleAverage_mono_on_of_le_circle (hci_lev y _) fun _ _ ↦ by split_ifs <;> norm_num
  have hcap_nonneg (y : ℝ) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ radialCapMean U ρ y c :=
    circleAverage_nonneg_of_nonneg fun z _ ↦ le_min (hUpos z) hc
  let A := fun y ↦ t * radialLevelFraction U ρ t y
  let G := fun y ↦ radialCapMean U ρ y (t * y)
  have hA : IntegrableOn A (Icc 0 1) := hlev_int.const_mul t
  have hG : IntegrableOn G (Icc 0 1) :=
    hint_comp ((hU.comp hpoint).inf (measurable_const.mul measurable_fst)) fun y hy ↦ by
      rw [Real.norm_of_nonneg (hcap_nonneg y (mul_nonneg ht hy.1))]
      exact (circleAverage_mono_on_of_le_circle (hci_cap _ _) fun _ _ ↦ min_le_right _ _).trans
        (mul_le_of_le_one_right ht hy.2)
  have hshift (y h : ℝ) (hy : 0 < y) (hh : 0 < h) (hyh : y + h < 1) :
      h * A (y + h) ≤ G (y + h) - G y := by
    have hc : t * y ≤ t * (y + h) := mul_le_mul_of_nonneg_left (by linarith) ht
    have hiL : CircleIntegrable
        (fun z ↦ (h * t) • (if t * (y + h) < U z then (1 : ℝ) else 0)) 0 (ρ (y + h)) :=
      (hci_lev (y + h) (ρ (y + h))).const_smul
    have havg := circleAverage_mono hiL
      ((hci_cap (t * (y + h)) (ρ (y + h))).sub (hci_cap (t * y) (ρ (y + h)))) fun z _ ↦ by
        dsimp only [Pi.sub_apply]
        by_cases hz : t * (y + h) < U z
        · rw [ite_eq_left hz, smul_eq_mul, mul_one, min_eq_right hz.le, min_eq_right (hc.trans hz.le)]
          linarith
        · rw [ite_eq_right hz, smul_eq_mul, mul_zero]
          exact sub_nonneg.mpr (min_le_min_left _ hc)
    rw [circleAverage_fun_smul, circleAverage_sub (hci_cap _ _) (hci_cap _ _), smul_eq_mul] at havg
    have hm := hmono (t * y) ⟨hy, by linarith⟩ ⟨by linarith, hyh⟩ (by linarith)
    dsimp [A, G]; linarith
  have hI {F : ℝ → ℝ} (hF : IntegrableOn F (Icc 0 1)) {u v : ℝ}
      (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) : IntervalIntegrable F volume u v :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr (hF.mono_set (Icc_subset_Icc hu hv))
  have hAu : IntegrableOn A (uIcc 0 1) := by simpa using hA
  have hprim : ContinuousOn (fun y ↦ ∫ t in (0 : ℝ)..y, A t) (Icc 0 1) := by
    simpa using intervalIntegral.continuousOn_primitive_interval hAu
  have hinner (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) : (∫ y in a..b, A y) ≤ M := by
    have hcont : ContinuousOn (fun h ↦ ∫ y in a + h..b + h, A y) (Icc 0 (1 - b)) := by
      have hleft := hprim.comp (continuous_const.add continuous_id).continuousOn
        (show MapsTo (fun h ↦ a + h) (Icc 0 (1 - b)) (Icc 0 1) from
          fun h hh ↦ ⟨by linarith [hh.1], by linarith [hh.2]⟩)
      have hright := hprim.comp (continuous_const.add continuous_id).continuousOn
        (show MapsTo (fun h ↦ b + h) (Icc 0 (1 - b)) (Icc 0 1) from
          fun h hh ↦ ⟨by linarith [hh.1], by linarith [hh.2]⟩)
      refine (hright.sub hleft).congr fun h hh ↦ ?_
      exact (intervalIntegral.integral_interval_sub_left
        (hI hA le_rfl (by linarith [hh.1]) (by linarith [hh.2]))
        (hI hA le_rfl (by linarith [hh.1]) (by linarith [hh.2]))).symm
    have hi : ∀ h ∈ Ioo (0 : ℝ) (1 - b), (∫ y in a + h..b + h, A y) ≤ M := by
      intro h ⟨hh, hbh'⟩
      have hbh : b + h < 1 := by linarith
      have habG := hI hG ha.le hab.le (by linarith)
      have hahG := hI hG ha.le (by linarith : a ≤ a + h) (by linarith)
      have hshG := hI hG (by linarith : 0 ≤ a + h) (by linarith : a + h ≤ b + h) hbh.le
      have hbhG := hI hG (by linarith : 0 ≤ b) (by linarith : b ≤ b + h) hbh.le
      have hshA := hI hA (by linarith : 0 ≤ a + h) (by linarith : a + h ≤ b + h) hbh.le
      have hAc : IntervalIntegrable (fun y ↦ A (y + h)) volume a b :=
        (IntervalIntegrable.comp_add_right_iff).mpr hshA
      have hGc : IntervalIntegrable (fun y ↦ G (y + h)) volume a b :=
        (IntervalIntegrable.comp_add_right_iff).mpr hshG
      have hmono' := intervalIntegral.integral_mono_on hab.le (hAc.const_mul h) (hGc.sub habG)
        fun y hy ↦ hshift y h (ha.trans_le hy.1) hh (by linarith [hy.2])
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hGc habG,
        intervalIntegral.integral_comp_add_right, intervalIntegral.integral_comp_add_right,
        intervalIntegral.integral_interval_sub_interval_comm' hshG habG hahG.symm] at hmono'
      have hlo : 0 ≤ ∫ y in a..a + h, G y :=
        intervalIntegral.integral_nonneg (by linarith) fun y hy ↦
          hcap_nonneg y (mul_nonneg ht (ha.trans_le hy.1).le)
      have hhi : (∫ y in b..b + h, G y) ≤ h * M := by
        simpa using intervalIntegral.integral_mono_on (by linarith) hbhG intervalIntegrable_const
          fun y hy ↦ hbound y ⟨by linarith [hy.1], hy.2.trans_lt hbh⟩ _
      exact (mul_le_mul_iff_of_pos_left hh).mp (by linarith)
    simpa using le_on_closure hi
      (by simpa only [closure_Ioo (by linarith : (0 : ℝ) ≠ 1 - b)] using hcont)
      continuousOn_const
      (show (0 : ℝ) ∈ closure (Ioo (0 : ℝ) (1 - b)) by
        rw [closure_Ioo (by linarith : (0 : ℝ) ≠ 1 - b)]; exact ⟨le_rfl, by linarith⟩)
  have hbnd : ∀ b ∈ Ioo (0 : ℝ) 1, (∫ y in (0 : ℝ)..b, A y) ≤ M := fun b hb ↦ by
    have hAb : IntegrableOn A (uIcc 0 b) := by
      rw [uIcc_of_le hb.1.le]; exact hA.mono_set (Icc_subset_Icc le_rfl hb.2.le)
    exact le_on_closure (s := Ioo (0 : ℝ) b) (f := fun a ↦ ∫ y in a..b, A y) (g := fun _ ↦ M)
      (fun a ha ↦ hinner a b ha.1 ha.2 hb.2)
      (by simpa only [closure_Ioo hb.1.ne, uIcc_of_le hb.1.le] using
        intervalIntegral.continuousOn_primitive_interval_left hAb)
      continuousOn_const (by simp [closure_Ioo hb.1.ne, hb.1.le])
  exact le_on_closure (f := fun b ↦ ∫ y in (0 : ℝ)..b, A y) (g := fun _ ↦ M) hbnd
    (by simpa using intervalIntegral.continuousOn_primitive_interval hAu)
    continuousOn_const (by simp)

/-- A radius whose exterior weighted disk has measure `y`. -/
def massRadius (α y : ℝ) : ℝ := sqrt (1 - y ^ (α + 1)⁻¹)

/-- The sharp positive weighted weak type bound for every admissible standard weight. -/
theorem isWeakTypeBound_weightedPositiveProjection {α : ℝ} (hα : -1 < α) :
    IsWeakTypeBound (weightedArea α) (weightedPositiveProjection α)
      (ENNReal.ofReal (gammaConstant α)) := by
  let := weightedArea_isProbabilityMeasure α hα
  have hp : 0 < α + 1 := by linarith
  have hD := gammaConstant_pos hα
  have hmr_unit {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : massRadius α y ∈ Ioo (0 : ℝ) 1 :=
    ⟨sqrt_pos.mpr (sub_pos.mpr (rpow_lt_one hy.1.le hy.2 (inv_pos.mpr hp))),
      (sqrt_lt' zero_lt_one).mpr (by simpa using sub_lt_self (1 : ℝ) (rpow_pos_of_pos hy.1 (α + 1)⁻¹))⟩
  have hg_inv {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : (1 - massRadius α y ^ 2) ^ (α + 1) = y := by
    rw [massRadius, sq_sqrt (sub_nonneg.mpr (rpow_lt_one hy.1.le hy.2 (inv_pos.mpr hp)).le),
      sub_sub_cancel, rpow_inv_rpow hy.1.le hp.ne']
  have hmr_inv {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : massRadius α ((1 - r ^ 2) ^ (α + 1)) = r := by
    rw [massRadius, rpow_rpow_inv (by nlinarith [hr.1, hr.2]) hp.ne', sub_sub_cancel, sqrt_sq hr.1.le]
  intro f hf t ht
  let s := t / gammaConstant α
  have hs : 0 < s := div_pos ht hD
  let U := weightedDiskPotential α f
  have hU : Measurable U := measurable_weightedDiskPotential hα hf
  have hi : (∫ y in (0 : ℝ)..1, s * radialLevelFraction U (massRadius α) s y) ≤
      ∫ w, ‖f w‖ ∂weightedArea α := by
    refine integral_mul_radialLevelFraction_le hU (weightedDiskPotential_nonneg α f)
      (by unfold massRadius; fun_prop) (fun c y hy u hu hyu ↦ ?_) (fun y hy c ↦ ?_) hs.le
    · exact antitoneOn_circleAverage_min_weightedDiskPotential hα hf c
        ⟨(hmr_unit hu).1.le, (hmr_unit hu).2⟩ ⟨(hmr_unit hy).1.le, (hmr_unit hy).2⟩
        (sqrt_le_sqrt (sub_le_sub_left (rpow_le_rpow hy.1.le hyu (inv_nonneg.mpr hp.le)) 1))
    · exact circleAverage_min_weightedDiskPotential_le_mass hα hf
        ⟨(hmr_unit hy).1.le, (hmr_unit hy).2⟩ c
  let S := disk ∩ {z : ℂ | s * (1 - ‖z‖ ^ 2) ^ (α + 1) < U z}
  have hS : MeasurableSet S := measurableSet_disk.inter (measurableSet_lt (by fun_prop) hU)
  have heq : (∫ y in (0 : ℝ)..1, radialLevelFraction U (massRadius α) s y) =
      (weightedArea α).real S := by
    have himg : (fun r : ℝ ↦ (1 - r ^ 2) ^ (α + 1)) '' Ioo 0 1 = Ioo 0 1 := by
      ext y; refine ⟨?_, fun hy ↦ ⟨massRadius α y, hmr_unit hy, hg_inv hy⟩⟩
      rintro ⟨r, hr, rfl⟩
      exact ⟨rpow_pos_of_pos (by nlinarith [hr.1, hr.2]) _,
        rpow_lt_one (by nlinarith [hr.1, hr.2]) (by nlinarith [hr.1]) hp⟩
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      ← integral_indicator_one hS,
      integral_weightedArea_eq_circleAverage hα ((integrable_const 1).indicator hS)]
    nth_rw 1 [← himg]
    rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun r hr ↦ (((hasDerivAt_pow 2 r).const_sub 1).rpow_const (p := α + 1)
        (Or.inl (by nlinarith [hr.1, hr.2]))).hasDerivWithinAt)
      (fun r hr u hu hru ↦ by rw [← hmr_inv hr, ← hmr_inv hu, hru])]
    refine setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
    rw [radialLevelFraction, hmr_inv hr]
    congr 1
    · rw [add_sub_cancel_right, show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat,
        show -(2 * r) * (α + 1) * (1 - r ^ 2) ^ α = -(2 * r * ((α + 1) * (1 - r ^ 2) ^ α)) by ring,
        abs_neg, abs_of_pos (mul_pos (mul_pos (by norm_num) hr.1)
          (mul_pos hp (rpow_pos_of_pos (by nlinarith [hr.1, hr.2]) _)))]
    · refine circleAverage_congr_sphere fun z hz ↦ ?_
      have hn : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right, abs_of_pos hr.1] using hz
      have hpred : z ∈ S ↔ s * (1 - r ^ 2) ^ (α + 1) < U z := by
        simp only [S, mem_inter_iff, mem_ofPred_eq, (mem_disk_iff z).mpr (hn.trans_lt hr.2),
          true_and, hn]
      by_cases hzS : z ∈ S
      · simp only [indicator_of_mem hzS, Pi.one_apply, ite_eq_left (hpred.mp hzS)]
      · simp only [indicator_of_notMem hzS, ite_eq_right (not_congr hpred |>.mp hzS)]
  rw [intervalIntegral.integral_const_mul, heq] at hi
  have hm : weightedArea α {z | ENNReal.ofReal t < weightedPositiveProjection α f z} ≤
      weightedArea α S := by
    apply measure_mono_ae
    filter_upwards [ae_mem_disk_weightedArea α] with z hz hlev
    refine ⟨hz, ?_⟩
    have hz1 := (mem_disk_iff z).mp hz
    have hJ : 0 < normalizer α ‖z‖ := normalizer_pos hα (by simpa using hz1)
    have hbound : (1 - ‖z‖ ^ 2) ^ (α + 1) * normalizer α ‖z‖ ≤ gammaConstant α := by
      rw [radialMass_mul_normalizer α (by simpa only [abs_norm] using hz1)]
      apply ge_of_tendsto (tendsto_circleAverage_boundaryPower hα)
      filter_upwards [Ioo_mem_nhdsLT hz1] with R hR
      simpa only [normalizer, sub_add_cancel, neg_neg] using
        normalizer_mono (-α - 2) (norm_nonneg z) hR.1.le hR.2
    have hF : t < weightedPotential α f z := by
      rw [weightedPotential_eq_toReal hα hf hz]
      exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le (weightedPositiveProjection_lt_top hα hf hz).ne).mp hlev
    show s * (1 - ‖z‖ ^ 2) ^ (α + 1) < weightedDiskPotential α f z
    rw [weightedDiskPotential_eq hz, weightedNormalizedPotential, lt_div_iff₀ hJ]
    have hscale := mul_le_mul_of_nonneg_left hbound hs.le
    rw [show s * gammaConstant α = t from div_mul_cancel₀ t hD.ne'] at hscale
    exact (show s * (1 - ‖z‖ ^ 2) ^ (α + 1) * normalizer α ‖z‖ =
      s * ((1 - ‖z‖ ^ 2) ^ (α + 1) * normalizer α ‖z‖) by ring).trans_le hscale |>.trans_lt hF
  have hmreal := ENNReal.toReal_mono (measure_ne_top _ _) hm
  have hreal : t * (weightedArea α).real {z | ENNReal.ofReal t < weightedPositiveProjection α f z} ≤
      gammaConstant α * ∫ w, ‖f w‖ ∂weightedArea α := by
    have hlarge := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hmreal hs.le).trans hi) hD.le
    simpa only [← mul_assoc, show gammaConstant α * s = t from mul_div_cancel₀ t hD.ne', measureReal_def] using! hlarge
  have he := ENNReal.ofReal_le_ofReal hreal
  rwa [ENNReal.ofReal_mul ht.le, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_mul hD.le, ofReal_integral_norm_eq_lintegral_enorm hf] at he

theorem weightedPositiveProjection_constant_eq (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (weightedPositiveProjection α) =
      ENNReal.ofReal (gammaConstant α) :=
  le_antisymm (sInf_le (isWeakTypeBound_weightedPositiveProjection hα))
    (gammaConstant_le_weightedPositiveProjection_constant α hα)

theorem weightedProjection_constant_le (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) ≤
      ENNReal.ofReal (gammaConstant α) :=
  (weakTypeConstant_mono fun f _ z ↦ by
    simpa only [weightedProjection, weightedPositiveProjection, enorm_mul, ofReal_norm] using
      enorm_integral_le_lintegral_enorm (μ := weightedArea α)
        (fun w ↦ weightedKernel α z w * f w)).trans_eq
    (weightedPositiveProjection_constant_eq α hα)

theorem isWeakTypeBound_positiveProjection_one :
    IsWeakTypeBound diskArea positiveProjection 1 := by
  have h := isWeakTypeBound_weightedPositiveProjection (α := 0) (by norm_num)
  rwa [weightedArea_zero, funext weightedPositiveProjection_zero, gammaConstant_zero,
    ENNReal.ofReal_one] at h

theorem positiveProjection_constant_eq_one : weakTypeConstant diskArea positiveProjection = 1 := by
  simpa [weightedArea_zero, funext weightedPositiveProjection_zero] using
    weightedPositiveProjection_constant_eq 0 (by norm_num)

theorem projection_constant_eq_one :
    weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) = 1 :=
  le_antisymm (by
    simpa [weightedArea_zero, show (fun f z ↦ ‖weightedProjection 0 f z‖ₑ) =
      (fun f z ↦ ‖projection f z‖ₑ) by ext; simp [weightedProjection, projection]] using
      weightedProjection_constant_le 0 (by norm_num)) one_le_projection_constant

end BergmanWeakType
