/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Reproduction
public import BergmanWeakType.Weighted.Normalizer
public import BergmanWeakType.Weighted.PolarIntegral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The explicit boundary lower bound for the complex weighted projection -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal Topology

namespace BergmanWeakType

/-- The boundary concentration lower bound uses ordinary integrable complex inputs. -/
theorem boundaryConstant_le_weightedProjection_constant (α : ℝ) (hα : 0 ≤ α) :
    ENNReal.ofReal (boundaryConstant α) ≤
      weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  have hα' : -1 < α := by linarith
  let := weightedArea_isProbabilityMeasure α hα'
  let boundaryCap (R : ℝ) : Set ℂ := disk ∩ Metric.ball 1 R
  let capProfile (R : ℝ) (u : ℂ) : ℝ :=
    if R * ‖u‖ ^ 2 < 2 * u.re then (2 * u.re - R * ‖u‖ ^ 2) ^ α else 0
  have hmeas (R : ℝ) : Measurable (capProfile R) :=
    (by fun_prop : Measurable fun u : ℂ ↦ (2 * u.re - R * ‖u‖ ^ 2) ^ α).ite
      (measurableSet_lt (by fun_prop) (by fun_prop)) measurable_const
  have hnn (R : ℝ) (u : ℂ) : 0 ≤ capProfile R u := by
    dsimp [capProfile]; split_ifs with h <;> [exact Real.rpow_nonneg (by linarith) _; exact le_rfl]
  have hle {R : ℝ} (hR : 0 ≤ R) {u : ℂ} (hu : u ∈ disk) : capProfile R u ≤ 2 ^ α := by
    dsimp [capProfile]; split_ifs with h
    · exact Real.rpow_le_rpow (by linarith) (by
        have := (mem_disk_iff u).mp hu
        nlinarith [Complex.re_le_norm u, mul_nonneg hR (sq_nonneg ‖u‖)]) hα
    · positivity
  have hint0 : (∫ z, capProfile 0 z ∂diskArea) = gammaConstant α / (α + 2) := by
    have hint : Integrable (capProfile 0) diskArea :=
      (integrable_const ((2 : ℝ) ^ α)).mono' (hmeas 0).aestronglyMeasurable
        (ae_mem_disk.mono fun z hz ↦ by rw [Real.norm_of_nonneg (hnn 0 z)]; exact hle le_rfl hz)
    rw [integral_diskArea_eq_circleAverage hint]
    have heq : (∫ r in Ioo (0 : ℝ) 1, (2 * r) • circleAverage (capProfile 0) 0 r) =
        gammaConstant α * ∫ r in Ioo (0 : ℝ) 1, r ^ (α + 1) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioo fun r ⟨hr, hr1⟩ ↦ ?_
      let H := fun θ ↦ capProfile 0 (circleMap 0 r (θ + -(π / 2)))
      have hpoint (θ : ℝ) : H θ = if 0 < sin θ then (2 * r) ^ α * sin θ ^ α else 0 := by
        dsimp only [H, capProfile]
        rw [zero_mul, sub_zero, circleMap_zero_re, ← sub_eq_add_neg, cos_sub_pi_div_two]
        simp only [mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < 2), mul_pos_iff_of_pos_left hr]
        split_ifs with hs
        · rw [show 2 * (r * sin θ) = (2 * r) * sin θ by ring]
          exact Real.mul_rpow (by positivity) hs.le
        · rfl
      have hii (a b : ℝ) (hab : a ≤ b) : IntervalIntegrable H volume a b := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
        refine Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
          ((hmeas 0).comp ((continuous_circleMap 0 r).comp
            (continuous_id.add_const _)).measurable).aestronglyMeasurable
          (M := (2 : ℝ) ^ α) (Filter.Eventually.of_forall fun θ ↦ ?_)
        rw [Real.norm_of_nonneg (hnn 0 _)]
        exact hle le_rfl (by simp [disk, abs_of_pos hr, hr1])
      have hleft : (∫ θ in (0 : ℝ)..π, H θ) = (2 * r) ^ α * ∫ θ in (0 : ℝ)..π, sin θ ^ α := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr_Ioo_of_le pi_pos.le fun θ hθ ↦ by
          rw [hpoint, ite_eq_left (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)]
      have hright : (∫ θ in π..2 * π, H θ) = 0 := by
        rw [← intervalIntegral.integral_zero (a := π) (b := 2 * π)]
        refine intervalIntegral.integral_congr_Ioo_of_le (by linarith [pi_pos]) fun θ hθ ↦ ?_
        have hs : sin θ ≤ 0 := by
          simpa using sin_nonpos_of_nonpos_of_neg_pi_le
            (by linarith [hθ.2] : θ - 2 * π ≤ 0) (by linarith [hθ.1] : -π ≤ θ - 2 * π)
        rw [hpoint, ite_eq_right (not_lt.mpr hs)]
      have havg : circleAverage (capProfile 0) 0 r = r ^ α * gammaConstant α / 2 := by
        rw [circleAverage_eq_integral_add (-(π / 2)), smul_eq_mul]
        change (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..2 * π, H θ) = _
        rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 π pi_pos.le)
          (hii π (2 * π) (by linarith [pi_pos])), hleft, hright, add_zero,
          integral_sin_rpow hα', Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le,
          gammaConstant_eq_boundaryGamma hα']
        have hs : sqrt π ^ 2 = π := sq_sqrt pi_pos.le
        have hsp : sqrt π ≠ 0 := (sqrt_pos.mpr pi_pos).ne'
        have hg : Real.Gamma (1 + α / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
        field_simp; nlinarith
      rw [havg, smul_eq_mul, Real.rpow_add hr, Real.rpow_one]; ring
    rw [heq, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_rpow (Or.inl (by linarith : -1 < α + 1)),
      one_rpow, zero_rpow (by linarith : α + 1 + 1 ≠ 0), sub_zero]
    ring
  have hint : Filter.Tendsto (fun R ↦ ∫ u, capProfile R u ∂diskArea) (𝓝[>] (0 : ℝ))
      (𝓝 (gammaConstant α / (α + 2))) := by
    rw [← hint0]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (2 : ℝ) ^ α)
      (Filter.Eventually.of_forall fun R ↦ (hmeas R).aestronglyMeasurable) ?_
      (integrable_const _) (Filter.Eventually.of_forall fun u ↦ ?_)
    · filter_upwards [self_mem_nhdsWithin] with R hR
      filter_upwards [ae_mem_disk] with u hu
      rw [Real.norm_of_nonneg (hnn R u)]
      exact hle (le_of_lt hR) hu
    · by_cases hu : 0 < 2 * u.re
      · have hbase : Filter.Tendsto (fun R : ℝ ↦ 2 * u.re - R * ‖u‖ ^ 2)
            (𝓝[>] (0 : ℝ)) (𝓝 (2 * u.re)) := by
          simpa only [zero_mul, sub_zero] using
            (by fun_prop : Continuous fun R : ℝ ↦ 2 * u.re - R * ‖u‖ ^ 2).continuousAt.tendsto.mono_left
              (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
        have hevent : ∀ᶠ R : ℝ in 𝓝[>] 0, R * ‖u‖ ^ 2 < 2 * u.re := by
          filter_upwards [hbase.eventually (lt_mem_nhds hu)] with R hR; linarith
        dsimp only [capProfile]
        rw [zero_mul, sub_zero, ite_eq_left hu]
        exact Filter.Tendsto.congr' (hevent.mono fun R hR ↦ by simp only [ite_eq_left hR])
          (hbase.rpow_const (Or.inl hu.ne'))
      · have heq : ∀ᶠ R : ℝ in 𝓝[>] 0, capProfile R u = 0 := by
          filter_upwards [self_mem_nhdsWithin] with R (hR : 0 < R)
          have hn : ¬ R * ‖u‖ ^ 2 < 2 * u.re := by
            nlinarith [le_of_not_gt hu, mul_nonneg hR.le (sq_nonneg ‖u‖)]
          simp only [capProfile, ite_eq_right hn]
        dsimp only [capProfile]
        rw [zero_mul, ite_eq_right hu]
        exact tendsto_const_nhds.congr' (heq.mono fun R hR ↦ hR.symm)
  have hrescaled : Filter.Tendsto (fun R ↦ R ^ (-(α + 2)) * (weightedArea α).real (boundaryCap R))
      (𝓝[>] (0 : ℝ)) (𝓝 (boundaryConstant α)) := by
    have hlim := (hint.const_mul (α + 1)).congr' <|
      eventually_mem_nhdsWithin.mono fun R (hR : 0 < R) ↦ by
        show (α + 1) * ∫ u, capProfile R u ∂diskArea =
          R ^ (-(α + 2)) * (weightedArea α).real (boundaryCap R)
        let g := (boundaryCap R).indicator (fun z : ℂ ↦ (1 - ‖z‖ ^ 2) ^ α)
        have hsq (u : ℂ) : 1 - ‖1 - (R : ℂ) * u‖ ^ 2 = R * (2 * u.re - R * ‖u‖ ^ 2) := by
          simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
            Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im]; ring
        have hcap_mem (u : ℂ) :
            1 - (R : ℂ) * u ∈ boundaryCap R ↔ u ∈ disk ∧ R * ‖u‖ ^ 2 < 2 * u.re := by
          have hd : 1 - (R : ℂ) * u ∈ disk ↔ R * ‖u‖ ^ 2 < 2 * u.re := by
            rw [mem_disk_iff]
            have := hsq u
            exact ⟨fun hu ↦ by nlinarith [norm_nonneg (1 - (R : ℂ) * u)],
              fun hu ↦ by nlinarith [norm_nonneg (1 - (R : ℂ) * u)]⟩
          have hball : 1 - (R : ℂ) * u ∈ Metric.ball 1 R ↔ u ∈ disk := by
            rw [Metric.mem_ball, dist_eq_norm, show 1 - (R : ℂ) * u - 1 = -((R : ℂ) * u) by ring,
              norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, mem_disk_iff]
            exact ⟨fun h ↦ by nlinarith, fun h ↦ by nlinarith⟩
          simp only [boundaryCap, Set.mem_inter_iff, hd, hball, and_comm]
        have haff (u : ℂ) : g (1 - (R : ℂ) * u) = R ^ α * disk.indicator (capProfile R) u := by
          dsimp only [g, capProfile]
          by_cases hu : u ∈ disk
          · rw [Set.indicator_of_mem hu]
            by_cases hp : R * ‖u‖ ^ 2 < 2 * u.re
            · rw [Set.indicator_of_mem ((hcap_mem u).mpr ⟨hu, hp⟩), ite_eq_left hp,
                hsq, Real.mul_rpow hR.le (by linarith)]
            · rw [Set.indicator_of_notMem (by simpa only [hcap_mem, hu, true_and] using hp),
                ite_eq_right hp, mul_zero]
          · rw [Set.indicator_of_notMem hu, mul_zero, Set.indicator_of_notMem]
            exact fun h ↦ hu ((hcap_mem u).mp h).1
        have hc := Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ)
          (fun z : ℂ ↦ g (1 - z)) R (hR := hR.le)
        rw [Complex.finrank_real_complex, integral_sub_left_eq_self g volume 1] at hc
        simp only [Complex.real_smul, smul_eq_mul] at hc
        have heq : ∫ u, g (1 - (R : ℂ) * u) ∂area = (R ^ 2)⁻¹ * ∫ z, g z ∂area := by
          simp only [area, integral_smul_measure, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi⁻¹),
            smul_eq_mul, hc]; ring
        simp_rw [haff] at heq
        rw [integral_const_mul, integral_indicator measurableSet_disk] at heq
        have hmass : (weightedArea α).real (boundaryCap R) = (α + 1) * ∫ z, g z ∂area := by
          rw [← integral_indicator_one (show MeasurableSet (boundaryCap R) from
              measurableSet_disk.inter Metric.isOpen_ball.measurableSet),
            integral_weightedArea_eq_diskArea hα', diskArea,
            ← integral_indicator measurableSet_disk, ← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
          by_cases hz : z ∈ boundaryCap R
          · simp [g, hz, hz.1]
          · by_cases hzd : z ∈ disk <;> simp [g, hz, hzd]
        have hrp : R ^ (-(α + 2)) = (R ^ α)⁻¹ * (R ^ 2)⁻¹ := by
          rw [← mul_inv, ← Real.rpow_natCast R 2, ← Real.rpow_add hR, ← Real.rpow_neg hR.le]
          push_cast; ring_nf
        change R ^ α * (∫ u, capProfile R u ∂diskArea) = _ at heq
        rw [hmass, hrp]
        linear_combination (α + 1) * (R ^ α)⁻¹ * heq -
          (α + 1) * (∫ u, capProfile R u ∂diskArea) * inv_mul_cancel₀ (Real.rpow_pos_of_pos hR α).ne'
    rwa [show (α + 1) * (gammaConstant α / (α + 2)) = boundaryConstant α by unfold boundaryConstant; ring] at hlim
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hrescaled)
  filter_upwards [self_mem_nhdsWithin] with R (hR : 0 < R)
  dsimp only [Function.comp_def]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _), measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  apply le_sInf
  intro C hC
  have hp : Filter.Tendsto (fun t : ℝ ↦ (R + 1 - t) ^ (-(α + 2))) (𝓝[<] 1) (𝓝 (R ^ (-(α + 2)))) := by
    have hc : ContinuousAt (fun t : ℝ ↦ (R + 1 - t) ^ (-(α + 2))) 1 :=
      (continuous_const.sub continuous_id).continuousAt.rpow_const
        (Or.inl (by change R + 1 - 1 ≠ 0; linarith))
    simpa only [add_sub_cancel_right] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ((ENNReal.continuous_mul_const (measure_ne_top (weightedArea α) (boundaryCap R)))
    |>.continuousAt.tendsto.comp (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp))
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ⟨ht, ht1⟩
  have ha : (t : ℂ) ∈ disk := by
    simp only [mem_disk_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.le, ht1]
  refine column_le_weakBound hα' hC ha Set.inter_subset_left (fun z hz ↦ ?_)
    (Real.rpow_pos_of_pos (by linarith) _)
  rw [norm_weightedKernel]
  refine Real.rpow_le_rpow_of_nonpos
    ((sub_pos.mpr ((mem_disk_iff z).mp hz.1)).trans_le (kernel_denominator_norm_lower z ha)) ?_
    (by linarith)
  have hz1 : ‖z‖ ≤ 1 := ((mem_disk_iff z).mp hz.1).le
  have hzR : ‖1 - z‖ < R := by simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz.2
  rw [show 1 - z * star (t : ℂ) = (1 - z) + (1 - (t : ℂ)) * z by
    simp only [Complex.star_def, Complex.conj_ofReal]; ring]
  calc
    _ ≤ ‖1 - z‖ + ‖(1 - (t : ℂ)) * z‖ := norm_add_le _ _
    _ = ‖1 - z‖ + (1 - t) * ‖z‖ := by
      rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht1)]
    _ ≤ R + 1 - t := by nlinarith

end BergmanWeakType
