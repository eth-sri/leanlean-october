module

public import PottsDiscontinuity.Analysis.Section4Series

/-! Pair τ with the sine kernel of the disk. Its Fourier coefficients give the
Abel means of the alternating tanh series. The linear vanishing of τ at zero
also permits passage to the boundary in the integral. -/

@[expose] public section

open Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity
open Bethe

private noncomputable def τc (lam α : ℝ) : ℝ := TcontFn lam α / (2 * π)

private theorem continuous_τc {lam : ℝ} (hlam : 0 < lam) : Continuous (τc lam) :=
  (continuous_TcontFn hlam).div_const _

private theorem τc_ae {lam : ℝ} (hlam : 0 < lam) :
    τc lam =ᵐ[volume.restrict (uIoc (-π) π)] tauSeries lam := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume π)] with α hα hn
  rw [uIoc_of_le (neg_le_self pi_nonneg)] at hα
  exact (tauSeries_eq hlam (abs_lt.mpr ⟨hα.1, hα.2.lt_of_ne hn⟩)).symm

private noncomputable def mode (lam : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) * tanh (lam * ((n + 1 : ℕ) : ℝ))

private theorem sinCoeff_τc {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    sinCoeff (τc lam) (n + 1) = mode lam n := by
  let s : ℝ → ℝ := fun x => sin (((n + 1 : ℕ) : ℝ) * x)
  have hs : Continuous s := by fun_prop
  have hU : sinCoeff (tauU lam) (n + 1) = π * tauCoeff lam n :=
    sinCoeff_trigSeries_succ (a := fun _ => 0) summable_zero (summable_tauCoeff hlam) 0 n
  have he (x : ℝ) : τc lam x * s x = (2 * π)⁻¹ * (-x * s x + tauU lam x * s x) := by
    unfold τc TcontFn
    ring
  change (∫ x in (-π)..π, τc lam x * s x) = _
  simp_rw [he]
  have h1 : IntervalIntegrable (fun x => -x * s x) volume (-π) π :=
    (continuous_neg.mul hs).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => tauU lam x * s x) volume (-π) π :=
    ((continuous_tauU hlam).mul hs).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1 h2]
  change (2 * π)⁻¹ * (sinCoeff (fun x => -x) (n+1) + sinCoeff (tauU lam) (n+1)) = _
  rw [sinCoeff_neg_id, hU]
  simp only [mode, tauCoeff, pow_succ']
  field_simp
  ring

private noncomputable def weight (lam : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * |tauCoeff lam n|

private theorem summable_weight {lam : ℝ} (hlam : 0 < lam) : Summable (weight lam) := by
  have hn : ‖exp (-lam)‖ < 1 := by simp [hlam]
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hn).summable
  have hs' : Summable (fun n : ℕ => ((n : ℝ) + 1) * exp (-lam) ^ (n + 1)) := by
    simpa using (summable_nat_add_iff 1).mpr hs
  refine Summable.of_norm_bounded (hs'.mul_left 2) fun n => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold weight; positivity)]
  unfold weight
  linarith [mul_le_mul_of_nonneg_left (abs_tauCoeff_le lam n) (by positivity : 0 ≤ (n : ℝ) + 1)]

private noncomputable def τBound (lam : ℝ) : ℝ := (1 + ∑' n, weight lam n) / (2 * π)

private theorem τBound_nonneg (lam : ℝ) : 0 ≤ τBound lam := by
  have : 0 ≤ ∑' n, weight lam n := tsum_nonneg fun _ => by unfold weight; positivity
  unfold τBound
  positivity

private theorem τc_bound {lam : ℝ} (hlam : 0 < lam) (α : ℝ) : |τc lam α| ≤ τBound lam * |α| := by
  let f (n : ℕ) := tauCoeff lam n * sin (((n + 1 : ℕ) : ℝ) * α)
  have h (n : ℕ) : ‖f n‖ ≤ weight lam n * |α| := by
    simp only [Real.norm_eq_abs, f, abs_mul, weight, Nat.cast_succ]
    rw [show ((n : ℝ) + 1) * |tauCoeff lam n| * |α| =
      |tauCoeff lam n| * (((n : ℝ) + 1) * |α|) by ring]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    simpa [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)] using
          Real.abs_sin_le_abs (x := ((n : ℝ) + 1) * α)
  have hb := (summable_weight hlam).mul_right |α|
  have hf := Summable.of_norm_bounded hb h
  have hsum : |tauU lam α| ≤ (∑' n, weight lam n) * |α| := by
    simp only [tauU, trigSeries, zero_mul, zero_add, ← Real.norm_eq_abs, ← tsum_mul_right]
    exact (norm_tsum_le_tsum_norm hf.norm).trans (hf.norm.tsum_le_tsum h hb)
  rw [τc, TcontFn, abs_div, abs_of_pos (by positivity : 0 < 2 * π), τBound]
  calc
    _ ≤ (|α| + (∑' n, weight lam n) * |α|) / (2 * π) := by
      gcongr
      exact (abs_add_le _ _).trans (by rw [abs_neg]; exact add_le_add_right hsum _)
    _ = _ := by ring

private theorem uIoc_subset : uIoc (-π) π ⊆ Icc (-π) π := by
  rw [uIoc_of_le (neg_le_self pi_nonneg)]
  exact Ioc_subset_Icc_self

private theorem τc_mul_sineKernel_hasSum {lam r : ℝ} (hlam : 0 < lam) (hr : r ∈ Ioo 0 1) :
    HasSum (fun n => mode lam n * r ^ (n+1)) (∫ α in (-π)..π, τc lam α * sineKernel r α) := by
  let F (n : ℕ) (x : ℝ) := r ^ (n+1) * (τc lam x * sin (((n + 1 : ℕ) : ℝ) * x))
  have hs := (summable_geometric_of_lt_one hr.1.le hr.2).mul_left (τBound lam * π * r)
  have hb : Summable (fun n : ℕ => (τBound lam * π) * r ^ (n+1)) := by
    simpa [pow_succ', ← mul_assoc] using hs
  have H := hasSum_intervalIntegral_of_boundOn (F := F)
    (fun n => continuous_const.mul ((continuous_τc hlam).mul (by fun_prop))) _ hb
    (by
      intro n x hx
      have hπ := abs_le.mpr (uIoc_subset hx)
      rw [show (|F n x|) = r ^ (n+1) * (|τc lam x| * |sin (((n+1 : ℕ) : ℝ) * x)|) by
        simp [F, abs_of_pos hr.1]]
      calc
        _ ≤ r ^ (n+1) * ((τBound lam * π) * 1) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr.1.le _)
          exact mul_le_mul ((τc_bound hlam x).trans (mul_le_mul_of_nonneg_left hπ (τBound_nonneg _)))
            (abs_sin_le_one _) (abs_nonneg _) (mul_nonneg (τBound_nonneg lam) pi_nonneg)
        _ = _ := by ring)
    (fun x => ((hasSum_sineKernel hr.1 hr.2 x).mul_left (τc lam x)).congr_fun fun n => by
      ring)
  refine H.congr_fun fun n => ?_
  symm
  change (∫ x in (-π)..π, r ^ (n+1) * (τc lam x * sin (((n+1 : ℕ) : ℝ) * x))) = _
  rw [intervalIntegral.integral_const_mul]
  change r ^ (n+1) * sinCoeff (τc lam) (n+1) = _
  rw [sinCoeff_τc hlam, mul_comm]

private theorem diskDen_lower (r x : ℝ) : 2*r*(1 - cos x) ≤ diskDen r x := by
  rw [diskDen_eq]
  nlinarith [sq_nonneg (1 - r)]

private theorem sineKernel_mul_abs_le {r x : ℝ} (hr : 0 < r) (hx : x ∈ Icc (-π) π) :
    |sineKernel r x| * |x| ≤ π ^ 2 / 4 := by
  by_cases hx0 : x = 0
  · simp [hx0]; positivity
  have hq := fourier_one_sub_cos_lower hx
  have hpos : 0 < 1 - cos x := (by positivity : 0 < 2*x^2/π^2).trans_le hq
  have hden : 0 < 2 * r * (1 - cos x) := by positivity
  have hl := diskDen_lower r x
  rw [sineKernel, abs_div, abs_mul, abs_of_pos hr, abs_of_pos (hden.trans_le hl)]
  calc
    _ ≤ r * |x| / (2 * r * (1 - cos x)) * |x| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left abs_sin_le_abs hr.le)
        (hden.trans_le hl).le).trans (div_le_div_of_nonneg_left (by positivity) hden hl)
    _ = x^2 / (2 * (1 - cos x)) := by
      rw [mul_assoc, div_mul_eq_mul_div, ← sq_abs]
      field_simp
    _ ≤ _ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity : 0 < π^2)] at hq
      nlinarith

private theorem measurable_τc_mul_sineKernel {lam r : ℝ} (hlam : 0 < lam) :
    Measurable (fun x => τc lam x * sineKernel r x) := by
  apply (continuous_τc hlam).measurable.mul
  unfold sineKernel diskDen
  fun_prop

private theorem τc_mul_sineKernel_bound {lam r x : ℝ} (hlam : 0 < lam) (hr : 0 < r)
    (hx : x ∈ uIoc (-π) π) : ‖τc lam x * sineKernel r x‖ ≤ τBound lam * (π ^ 2 / 4) := by
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ (τBound lam * |x|) * |sineKernel r x| := by gcongr; exact τc_bound hlam x
    _ = τBound lam * (|sineKernel r x| * |x|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sineKernel_mul_abs_le hr (uIoc_subset hx)) (τBound_nonneg _)

private theorem integral_τc_mul_sineKernel_tendsto {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun r => ∫ x in (-π)..π, τc lam x * sineKernel r x) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ x in (-π)..π, τc lam x * sineKernel 1 x)) := by
  have hR : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r ∈ Ioo 0 1 := Ioo_mem_nhdsLT (by norm_num)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => τBound lam * (π ^ 2 / 4))
    (Eventually.of_forall fun _ => (measurable_τc_mul_sineKernel hlam).aestronglyMeasurable)
    (hR.mono fun r hr =>
      ae_of_all volume fun x hx => τc_mul_sineKernel_bound hlam hr.1 hx)
    intervalIntegrable_const ?_
  filter_upwards [Measure.ae_ne volume 0] with x hx0 hx
  have hq := fourier_one_sub_cos_lower (uIoc_subset hx)
  have hpos : 0 < 1 - cos x := (by positivity : 0 < 2*x^2/π^2).trans_le hq
  have hd : diskDen 1 x ≠ 0 := by rw [diskDen_eq]; positivity
  have h : ContinuousAt (fun r => sineKernel r x) 1 := by
    have hf : Continuous (fun r : ℝ => r * sin x) := by fun_prop
    have hg : Continuous (fun r : ℝ => diskDen r x) := by unfold diskDen; fun_prop
    exact hf.continuousAt.div hg.continuousAt hd
  exact tendsto_const_nhds.mul (h.tendsto.mono_left nhdsWithin_le_nhds)

private theorem τc_mul_sineKernel_integrable {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) :
    IntervalIntegrable (fun x => τc lam x * sineKernel r x) volume (-π) π := by
  apply IntervalIntegrable.mono_fun' (g := fun _ => τBound lam * (π ^ 2 / 4)) intervalIntegrable_const
    (measurable_τc_mul_sineKernel hlam).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  exact τc_mul_sineKernel_bound hlam hr hx

/-- The logarithmic derivative integral, from the radial boundary value of the sine kernel. -/
theorem fourierPPrime_tauSeries_integral {lam : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ, Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      log (cosh lam) - (∫ x in (-π)..π, fourierPPrime lam x * tauSeries lam x) = lam + 2*S := by
  obtain ⟨S, _, hS, _, _, _⟩ := identity44 lam hlam
  have hS' := hS
  refine ⟨S, hS', ?_⟩
  have hb (N : ℕ) : (∑ n ∈ Finset.range N, mode lam n) = altTanhPartial lam N := by
    rw [altTanhPartial, sum_Icc_one_eq_sum_range]
    simp [mode, mul_comm lam]
  have hbS := hS'.congr fun N => (hb N).symm
  have hR : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r ∈ Ioo 0 1 := Ioo_mem_nhdsLT (by norm_num)
  have hlim :=
    tendsto_nhds_unique (integral_τc_mul_sineKernel_tendsto hlam)
      ((tendsto_abel_succ hbS).congr' (hR.mono
        fun _ hr => (τc_mul_sineKernel_hasSum hlam hr).tsum_eq))
  let r := exp (-2*lam)
  have hr : r ∈ Ioo 0 1 := ⟨exp_pos _, exp_lt_one_iff.mpr (by linarith)⟩
  have hfinite (N : ℕ) : (∑ n ∈ Finset.range N, mode lam n * r ^ (n+1)) =
      -logCoshExpPartial lam N - ∑ n ∈ Finset.range N, mode lam n := by
    rw [logCoshExpPartial, sum_Icc_one_eq_sum_range, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have he : r ^ (n+1) = exp (-2 * (lam * ((n+1 : ℕ) : ℝ))) := by
      dsimp [r]
      rw [← exp_nat_mul]
      congr 1 <;> ring
    rw [he]
    unfold mode logCoshExpTerm
    rw [show -2 * lam * ((n+1 : ℕ) : ℝ) = -2 * (lam * ((n+1 : ℕ) : ℝ)) by ring, Nat.cast_succ]
    linear_combination ((-1 : ℝ) ^ (n+1) / ((n : ℝ) + 1)) * tanh_exp_identity (lam * ((n : ℝ) + 1))
  have hsm := tendsto_nhds_unique (τc_mul_sineKernel_hasSum hlam hr).tendsto_sum_nat
    (((tendsto_logCoshExpPartial hlam).neg.sub hbS).congr fun N => (hfinite N).symm)
  have hprofile (x : ℝ) : fourierPPrime lam x = sineKernel r x - sineKernel 1 x := by
    have h1 : sineKernel 1 x = 1/2 * (sin x / (1 - cos x)) := by
      simpa using sineKernel_exp_neg 0 x
    rw [show r = exp (-(2*lam)) by dsimp [r]; congr 1 <;> ring, sineKernel_exp_neg, h1]
    by_cases hx : x = 0
    · simp [fourierPPrime, hx]
    · simp only [fourierPPrime, hx, ite_false]; ring
  rw [integral_congr_ae_restrict ((τc_ae hlam).symm.mono fun x hx => congrArg (fourierPPrime lam x * ·) hx)]
  simp_rw [hprofile, sub_mul, mul_comm _ (τc lam _)]
  rw [intervalIntegral.integral_sub (τc_mul_sineKernel_integrable hlam hr.1)
    (τc_mul_sineKernel_integrable hlam zero_lt_one), hlim, hsm]
  ring

end PottsDiscontinuity
