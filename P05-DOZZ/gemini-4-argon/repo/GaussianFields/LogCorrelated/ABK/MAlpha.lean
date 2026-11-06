/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Power

/-!
# GaussianFields.LogCorrelated/ABK/MAlpha

Port of the corresponding GaussianFields source module.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields

/-- Finite-interval integral of `t^(α-1)`. -/
theorem integral_interval_rpow_sub_one {α a b : ℝ} (hα : 0 < α) :
    (∫ t in a..b, t ^ (α - 1) ∂(volume : Measure ℝ)) =
      (b ^ α - a ^ α) / α := by
  rw [integral_rpow (Or.inl (by linarith : -1 < α - 1))]
  ring_nf

/-- Uniform bound for an Abel-density interval integral. -/
theorem abs_alpha_mul_integral_interval_rpow_mul_le {α a b C : ℝ}
    {F : ℝ → ℝ} (hα : 0 < α) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbound : ∀ t ∈ Set.Ioc a b, |F t| ≤ C) :
    |α * ∫ t in a..b, t ^ (α - 1) * F t ∂(volume : Measure ℝ)| ≤
      C * (b ^ α - a ^ α) := by
  have hbound_ae :
      ∀ᵐ t : ℝ, t ∈ Set.Ioc a b →
        ‖t ^ (α - 1) * F t‖ ≤ C * t ^ (α - 1) := by
    filter_upwards with t ht
    have hpow_nonneg := Real.rpow_nonneg ((lt_of_le_of_lt ha ht.1).le) (α - 1)
    calc
      ‖t ^ (α - 1) * F t‖ = t ^ (α - 1) * |F t| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow_nonneg]
      _ ≤ t ^ (α - 1) * C := mul_le_mul_of_nonneg_left (hbound t ht) hpow_nonneg
      _ = C * t ^ (α - 1) := by ring
  calc
    |α * ∫ t in a..b, t ^ (α - 1) * F t ∂(volume : Measure ℝ)|
        = α * ‖∫ t in a..b, t ^ (α - 1) * F t ∂(volume : Measure ℝ)‖ := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos hα]
    _ ≤ α * ∫ t in a..b, C * t ^ (α - 1) ∂(volume : Measure ℝ) :=
          mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab hbound_ae ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < α - 1)).const_mul C)) hα.le
    _ = α * (C * ((b ^ α - a ^ α) / α)) := by rw [(show ∫ t in a..b, C * t ^ (α - 1) ∂(volume : Measure ℝ) = C * ((b ^ α - a ^ α) / α) by rw [intervalIntegral.integral_const_mul, integral_interval_rpow_sub_one hα])]
    _ = C * (b ^ α - a ^ α) := by
          field_simp [hα.ne']







/-- The Appendix A limit `α M_α^{-1} → M_0`. -/
theorem tendsto_alpha_mul_abkMAlphaInv {d} (hd : 0 < d)
    (ζ : ABKCutoff d) :
    Tendsto (fun α : ℝ => α * abkMAlphaInv ζ α)
      (𝓝[>] (0 : ℝ)) (𝓝 (abkM0 ζ)) := by
  have tendsto_alpha_mul_integral_Ioc_two_abkSelfConvolution : Tendsto (fun α : ℝ => α * ∫ t in Set.Ioc (0 : ℝ) 2, t ^ (α - 1) * abkCutoffSelfConvolution ζ (abkRadialPoint d t) ∂(volume : Measure ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (abkM0 ζ)) := by
    have continuous_abkCutoffSelfConvolution_radialProfile : Continuous (fun t : ℝ => abkCutoffSelfConvolution ζ (abkRadialPoint d t)) := by
      exact (continuous_abkCutoffSelfConvolution ζ).comp (by
        refine continuous_pi ?_
        intro i
        by_cases hi : (i : Nat) = 0
        · simp only [abkRadialPoint, ite_eq_left hi]
          continuity
        · simpa [abkRadialPoint, hi] using continuous_const)
    have tendsto_alpha_mul_integral_interval_rpow {A} {B} {F : ℝ → ℝ} (hA : 0 < A) (hsmall : ∀ ε > 0, ∃ δ, 0 < δ ∧ δ ≤ A ∧ ∀ t ∈ Set.Ioc (0 : ℝ) δ, |F t - F 0| ≤ ε) (hbound : ∀ t ∈ Set.Ioc (0 : ℝ) A, |F t - F 0| ≤ B) (hint : ∀ α : ℝ, 0 < α → IntervalIntegrable (fun t : ℝ => t ^ (α - 1) * (F t - F 0)) (volume : Measure ℝ) 0 A) : Tendsto (fun α : ℝ => α * ∫ t in (0 : ℝ)..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) := by
      have tendsto_alpha_mul_integral_interval_rpow_mul_zero {A} {B} {F : ℝ → ℝ} (hA : 0 < A) (hsmall : ∀ ε > 0, ∃ δ, 0 < δ ∧ δ ≤ A ∧ ∀ t ∈ Set.Ioc (0 : ℝ) δ, |F t| ≤ ε) (hbound : ∀ t ∈ Set.Ioc (0 : ℝ) A, |F t| ≤ B) (hint : ∀ α : ℝ, 0 < α → IntervalIntegrable (fun t : ℝ => t ^ (α - 1) * F t) (volume : Measure ℝ) 0 A) : Tendsto (fun α : ℝ => α * ∫ t in (0 : ℝ)..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        rw [Metric.tendsto_nhds]
        intro ε hε
        let η : ℝ := ε / 4
        rcases hsmall η (by dsimp [η]; positivity) with ⟨δ, hδ_pos, hδ_le, hδ_small⟩
        have hδ_tendsto :
            Tendsto (fun α : ℝ => δ ^ α) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
          simpa using (Real.continuousAt_const_rpow (a := δ) (b := 0) hδ_pos.ne').mono_left nhdsWithin_le_nhds
        filter_upwards [self_mem_nhdsWithin, ((Metric.tendsto_nhds.mp (by simpa using ((show Tendsto (fun α : ℝ => A ^ α) (𝓝[>] (0 : ℝ)) (𝓝 1) by simpa using (Real.continuousAt_const_rpow (a := A) (b := 0) hA.ne').mono_left nhdsWithin_le_nhds).sub hδ_tendsto).const_mul B) (ε / 2) (by positivity)) : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), dist (B * (A ^ α - δ ^ α)) 0 < ε / 2), ((show Tendsto (fun α : ℝ => η * δ ^ α) (𝓝[>] (0 : ℝ)) (𝓝 η) by simpa using hδ_tendsto.const_mul η).eventually (Iio_mem_nhds (by dsimp [η]; linarith)) : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), η * δ ^ α < ε / 2)] with
          α hα_pos htail hnear
        have hα := hα_pos
        have hInt0A := hint α hα
        have hmain :
            |α * ∫ t in (0 : ℝ)..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)| < ε := by
          calc
            |α * ∫ t in (0 : ℝ)..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)|
                = |α * ∫ t in (0 : ℝ)..δ, t ^ (α - 1) * F t ∂(volume : Measure ℝ) +
                    α * ∫ t in δ..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)| := by
                  rw [(show (∫ t in (0 : ℝ)..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)) = (∫ t in (0 : ℝ)..δ, t ^ (α - 1) * F t ∂(volume : Measure ℝ)) + ∫ t in δ..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ) by rw [← intervalIntegral.integral_add_adjacent_intervals (hInt0A.mono_set (Set.uIcc_subset_uIcc (by rw [Set.mem_uIcc]; exact Or.inl ⟨le_rfl, hA.le⟩) (by rw [Set.mem_uIcc]; exact Or.inl ⟨hδ_pos.le, hδ_le⟩))) (hInt0A.mono_set (Set.uIcc_subset_uIcc (by rw [Set.mem_uIcc]; exact Or.inl ⟨hδ_pos.le, hδ_le⟩) (by rw [Set.mem_uIcc]; exact Or.inl ⟨hA.le, le_rfl⟩)))])]
                  ring_nf
            _ ≤ |α * ∫ t in (0 : ℝ)..δ, t ^ (α - 1) * F t ∂(volume : Measure ℝ)| +
                  |α * ∫ t in δ..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)| :=
                  abs_add_le _ _
            _ ≤ η * δ ^ α + B * (A ^ α - δ ^ α) :=
                  add_le_add (by simpa [(Real.zero_rpow hα.ne')] using (abs_alpha_mul_integral_interval_rpow_mul_le (α := α) (a := 0) (b := δ) (C := η) (F := F) hα (by norm_num) hδ_pos.le hδ_small)) (by exact abs_alpha_mul_integral_interval_rpow_mul_le (α := α) (a := δ) (b := A) (C := B) (F := F) hα hδ_pos.le hδ_le (fun t ht => hbound t ⟨hδ_pos.trans ht.1, ht.2⟩))
            _ ≤ η * δ ^ α + |B * (A ^ α - δ ^ α)| :=
                  by
                    simpa [add_comm, add_left_comm, add_assoc] using
                      add_le_add_left (le_abs_self (B * (A ^ α - δ ^ α))) (η * δ ^ α)
            _ < ε / 2 + ε / 2 := add_lt_add hnear (by simpa [Real.dist_eq, Real.norm_eq_abs] using htail)
            _ = ε := by ring
        simpa [Real.dist_eq, Real.norm_eq_abs] using hmain
      let G : ℝ → ℝ := fun t => F t - F 0
      refine (show Tendsto (fun α : ℝ => α * ∫ t in (0 : ℝ)..A, t ^ (α - 1) * G t ∂(volume : Measure ℝ) + F 0 * A ^ α) (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) by simpa using ((tendsto_alpha_mul_integral_interval_rpow_mul_zero (A := A) (B := B) (F := G) hA hsmall hbound hint).add (by simpa using (show Tendsto (fun α : ℝ => A ^ α) (𝓝[>] (0 : ℝ)) (𝓝 1) by simpa using (Real.continuousAt_const_rpow (a := A) (b := 0) hA.ne').mono_left nhdsWithin_le_nhds).const_mul (F 0)))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with α hα_mem
      have hα : 0 < α := hα_mem
      symm
      calc
        α * ∫ t in (0 : ℝ)..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)
            = α * ∫ t in (0 : ℝ)..A,
                (t ^ (α - 1) * G t + F 0 * t ^ (α - 1)) ∂(volume : Measure ℝ) := by
              congr 1
              refine intervalIntegral.integral_congr ?_
              intro t _ht
              dsimp [G]
              ring_nf
        _ = α *
            ((∫ t in (0 : ℝ)..A, t ^ (α - 1) * G t ∂(volume : Measure ℝ)) +
              ∫ t in (0 : ℝ)..A, F 0 * t ^ (α - 1) ∂(volume : Measure ℝ)) := by
              rw [intervalIntegral.integral_add (hint α hα) ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < α - 1)).const_mul (F 0))]
        _ = α * (∫ t in (0 : ℝ)..A, t ^ (α - 1) * G t ∂(volume : Measure ℝ)) +
            F 0 * A ^ α := by
              rw [intervalIntegral.integral_const_mul, integral_interval_rpow_sub_one hα, (Real.zero_rpow hα.ne')]
              field_simp [hα.ne']
              ring
    let F : ℝ → ℝ := fun t => abkCutoffSelfConvolution ζ (abkRadialPoint d t)
    have hF_cont := continuous_abkCutoffSelfConvolution_radialProfile
    have hF0 : F 0 = abkM0 ζ := (show abkCutoffSelfConvolution ζ (abkRadialPoint d 0) = abkM0 ζ by rw [(show abkRadialPoint d 0 = (0 : Vec d) by ext i; simp [abkRadialPoint]), abkCutoffSelfConvolution_zero])
    rcases (isCompact_Icc.bddAbove_image ((hF_cont.sub continuous_const).abs).continuousOn) with ⟨B, hB⟩
    have hsmall :
        ∀ ε > 0, ∃ δ, 0 < δ ∧ δ ≤ (2 : ℝ) ∧
          ∀ t ∈ Set.Ioc (0 : ℝ) δ, |F t - F 0| ≤ ε := by
      intro ε hε
      rcases (Metric.tendsto_nhdsWithin_nhds.mp (hF_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)) ε hε with
        ⟨δ₀, hδ₀_pos, hδ₀⟩
      refine ⟨min (δ₀ / 2) 2, ?_, min_le_right _ _, ?_⟩
      · exact lt_min (half_pos hδ₀_pos) (by norm_num)
      · intro t ht
        have hdist : dist t 0 < δ₀ := by
          calc
            dist t 0 = t := by
              rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1.le]
            _ ≤ min (δ₀ / 2) 2 := ht.2
            _ ≤ δ₀ / 2 := min_le_left _ _
            _ < δ₀ := by linarith
        exact le_of_lt (by simpa [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using (hδ₀ ht.1 hdist))
    refine (show Tendsto (fun α : ℝ => α * ∫ t in (0 : ℝ)..(2 : ℝ), t ^ (α - 1) * F t ∂(volume : Measure ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (abkM0 ζ)) by simpa [hF0] using (tendsto_alpha_mul_integral_interval_rpow (A := (2 : ℝ)) (B := B) (F := F) (by norm_num : (0 : ℝ) < 2) hsmall (by intro t ht; exact hB ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩) (by intro α hα; exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < α - 1)).mul_continuousOn ((hF_cont.sub continuous_const).continuousOn)))).congr' ?_
    filter_upwards with α
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  have abkMAlphaInv_eq_integral_Ioc_two (α : ℝ) : abkMAlphaInv ζ α = ∫ t in Set.Ioc (0 : ℝ) 2, t ^ (α - 1) * abkCutoffSelfConvolution ζ (abkRadialPoint d t) ∂(volume : Measure ℝ) := by
    rw [abkMAlphaInv_eq_integral_rpow_selfConvolution ζ α]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi ?_ ?_
    · exact Set.Ioc_subset_Ioi_self
    · intro t ht
      rw [abkCutoffSelfConvolution_radial_eq_zero_of_two_lt hd ζ (lt_of_not_ge (show ¬ t ≤ 2 by intro ht_le; exact ht.2 ⟨ht.1, ht_le⟩)), mul_zero]
  refine (tendsto_alpha_mul_integral_Ioc_two_abkSelfConvolution).congr' ?_
  filter_upwards with α
  rw [abkMAlphaInv_eq_integral_Ioc_two α]

/-- Scalar logarithmic limit used in the covariance computation:
`(ρ^{-α} - 1) / α → -log ρ` as `α → 0+`. -/
theorem tendsto_rpow_neg_sub_one_div_nhdsGT_zero {ρ} (hρ : 0 < ρ) :
    Tendsto (fun α : ℝ => (ρ ^ (-α) - 1) / α)
      (𝓝[>] (0 : ℝ)) (𝓝 (-Real.log ρ)) := by
  have hmono : 𝓝[>] (0 : ℝ) ≤ nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ) := by
    refine nhdsWithin_mono _ ?_
    intro x hx
    simp [hx.ne']
  refine ((show HasDerivAt (fun α : ℝ => ρ ^ (-α)) (-Real.log ρ) 0 by simpa [Real.rpow_zero] using ((hasDerivAt_neg' (0 : ℝ)).const_rpow hρ)).tendsto_slope_zero.mono_left hmono).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  rw [zero_add, neg_zero, Real.rpow_zero]
  change α⁻¹ * (ρ ^ (-α) - 1) = (ρ ^ (-α) - 1) / α
  rw [div_eq_mul_inv]
  ring

end GaussianFields

end
