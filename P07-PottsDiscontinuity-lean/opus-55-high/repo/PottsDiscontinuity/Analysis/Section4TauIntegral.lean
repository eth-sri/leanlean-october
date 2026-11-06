module

public import Mathlib
public import PottsDiscontinuity.Analysis.Section4Series

/-!
# The explicit τ integral in Section 4

The literal τ series is interpreted by its ordered partial sums.  This file uses Abel means of
that series.  The Poisson regularization splits into a sawtooth term and an exponentially
convergent correction, which gives the uniform local bound needed against the singular `P'`.
-/

public noncomputable section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

def fourierPrimeControl (lam : ℝ) : ℝ :=
  (π / (Real.cosh (2 * lam) - 1) + π ^ 2 / 2) / 2

theorem fourierPPrime_alpha_bound {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α| * |α| ≤ fourierPrimeControl lam := by
  have hcosh : 1 < Real.cosh (2 * lam) := by aesop
  by_cases hα0 : α = 0
  · simp [fourierPPrime, hα0, fourierPrimeControl]
    positivity
  have hcosLower := (div_le_iff₀ (by positivity)).1 (Bethe.ratio_one_sub_cos_lower hα)
  have hd : 0 < 1 - Real.cos α := by nlinarith [sq_pos_of_ne_zero hα0]
  have hs := Real.abs_sin_le_one α
  have hs2 := mul_le_mul_of_nonneg_right (Real.abs_sin_le_abs (x := α)) (abs_nonneg α)
  have hαπ := abs_le.2 hα
  have h1 : |Real.sin α / (Real.cosh (2 * lam) - Real.cos α)| * |α| ≤
      π / (Real.cosh (2 * lam) - 1) := by
    rw [abs_div, abs_of_pos (by linarith [Real.cos_le_one α] :
      0 < Real.cosh (2 * lam) - Real.cos α), div_mul_eq_mul_div]
    gcongr
    · simpa using mul_le_mul hs hαπ (abs_nonneg _) zero_le_one
    · exact Real.cos_le_one α
  have h2 : |Real.sin α / (1 - Real.cos α)| * |α| ≤ π ^ 2 / 2 := by
    rw [abs_div, abs_of_pos hd, div_mul_eq_mul_div, div_le_iff₀ hd]
    linarith [abs_mul_abs_self α]
  rw [fourierPPrime, ite_eq_right hα0, fourierPrimeControl, abs_mul, abs_of_pos one_half_pos]
  nlinarith [abs_sub (Real.sin α / (Real.cosh (2 * lam) - Real.cos α))
    (Real.sin α / (1 - Real.cos α)), abs_nonneg α]

def tauFourierTerm (lam α : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / (π * ((n : ℝ) + 1)) *
    Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) * Real.sin (((n + 1 : ℕ) : ℝ) * α)

section
variable (lam μ α : ℝ)
def tauAbel  : ℝ :=
  ∑' n : ℕ, tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1)

def tauAbelCorrectionCoeff (n : ℕ) : ℝ :=
  (1 / (2 * π) : ℝ) * Real.exp (-μ) ^ (n + 1) * Bethe.tauCoeff lam n

def tauAbelCorrectionTerm (n : ℕ) : ℝ :=
  tauAbelCorrectionCoeff lam μ n * Real.sin (((n + 1 : ℕ) : ℝ) * α)
end

theorem abs_sin_succ_le (n : ℕ) (α : ℝ) :
    |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤ ((n : ℝ) + 1) * |α| :=
  Real.abs_sin_le_abs.trans_eq (by rw [abs_mul, Nat.abs_cast]; push_cast; ring)

section
variable {lam μ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ)
include hμ in
theorem abs_tauAbelCorrectionCoeff_le (n : ℕ) :
    |tauAbelCorrectionCoeff lam μ n| ≤ 1 / (2 * π) * |Bethe.tauCoeff lam n| := by
  rw [tauAbelCorrectionCoeff, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
  have : |Real.exp (-μ) ^ (n + 1)| ≤ 1 := by
    simp
    exact pow_le_one₀ (by positivity) (by simp; linarith)
  nlinarith [mul_le_mul_of_nonneg_right this (abs_nonneg (Bethe.tauCoeff lam n)),
    (by positivity : (0 : ℝ) < 1 / (2 * π))]

include hlam hμ

theorem summable_tauAbelCorrectionCoeff : Summable (tauAbelCorrectionCoeff lam μ) :=
  .of_norm_bounded ((Bethe.summable_tauCoeff hlam).abs.mul_left _)
    (abs_tauAbelCorrectionCoeff_le hμ)

theorem summable_tauAbelCorrection (α : ℝ) :
    Summable (tauAbelCorrectionTerm lam μ α) :=
  .of_norm_bounded (summable_tauAbelCorrectionCoeff hlam hμ).abs fun _ =>
    (abs_mul _ _).trans_le (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))

theorem hasSum_tauAbel (α : ℝ) :
    HasSum (fun n => tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1))
      ((1 / (2 * π) : ℝ) * Bethe.sawS μ α + ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n) := by
  rw [← Bethe.xiConv_neg_id hμ]
  convert ((Bethe.hasSum_xiConv_neg_id hμ α).mul_left (1 / (2 * π))).add
    (summable_tauAbelCorrection hlam hμ α).hasSum using 1
  funext n
  grind [tauFourierTerm, tauAbelCorrectionTerm, tauAbelCorrectionCoeff, Bethe.tauCoeff]

theorem tauAbel_eq_sawS_add_correction (α : ℝ) :
    tauAbel lam μ α = (1 / (2 * π) : ℝ) * Bethe.sawS μ α +
      ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n :=
  (hasSum_tauAbel hlam hμ α).tsum_eq
end

theorem summable_tauCoeff_weighted {lam : ℝ} (hlam : 0 < lam) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * |Bethe.tauCoeff lam n|) := by
  have h := (summable_nat_add_iff 1 (f := fun n : ℕ => (n : ℝ) ^ 1 * Real.exp (-lam) ^ n)).2
    (summable_pow_mul_geometric_of_norm_lt_one 1 (by simp [hlam]))
  refine .of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h.mul_left 2)
  push_cast at *
  nlinarith [Bethe.abs_tauCoeff_le lam n]

def tauCoeffWeightedSum (lam : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) * |Bethe.tauCoeff lam n|

theorem tauAbelCorrection_abs_bound {lam μ α : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) :
    |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| ≤
      (1 / (2 * π) : ℝ) * |α| * tauCoeffWeightedSum lam := by
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded ((summable_tauCoeff_weighted hlam).hasSum.mul_left _) fun n => ?_
  rw [Real.norm_eq_abs, tauAbelCorrectionTerm, abs_mul]
  calc _ ≤ 1 / (2 * π) * |Bethe.tauCoeff lam n| * (((n : ℝ) + 1) * |α|) :=
        mul_le_mul (abs_tauAbelCorrectionCoeff_le hμ n) (abs_sin_succ_le n α)
          (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem sawS_abs_le_two_mul_abs {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    |Bethe.sawS μ α| ≤ 2 * |α| := by
  rw [Bethe.sawS_eq_arctan hμ α, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
  by_cases hα : |α| ≤ π / 2
  · have hden : 1 ≤ Real.exp μ + Real.cos α := by
      linarith [Real.cos_nonneg_of_mem_Icc (abs_le.mp hα), Real.one_lt_exp_iff.2 hμ]
    have := Real.abs_arctan_le_abs (x := Real.sin α / (Real.exp μ + Real.cos α))
    rw [abs_div, abs_of_pos (by linarith : 0 < Real.exp μ + Real.cos α)] at this
    linarith [div_le_self (abs_nonneg (Real.sin α)) hden, Real.abs_sin_le_abs (x := α)]
  · linarith [abs_lt.2 ⟨Real.neg_pi_div_two_lt_arctan (Real.sin α / (Real.exp μ + Real.cos α)),
      Real.arctan_lt_pi_div_two _⟩]

section
variable {lam μ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ)
include hlam hμ
theorem continuous_tauAbel : Continuous (tauAbel lam μ) := by
  convert ((continuous_iff_continuousAt.2 fun α => (Bethe.hasDerivAt_sawS hμ α).continuousAt).const_mul
    (1 / (2 * π))).add (Bethe.continuous_trigSeries summable_zero
      (summable_tauAbelCorrectionCoeff hlam hμ) 0) using 1
  funext α
  simp [tauAbel_eq_sawS_add_correction hlam hμ, tauAbelCorrectionTerm, Bethe.trigSeries]
end

theorem measurable_fourierPPrime (lam : ℝ) : Measurable (fourierPPrime lam) :=
  Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

def fourierTauProductControl (lam : ℝ) : ℝ :=
  fourierPrimeControl lam * (1 / (2 * π) * (2 + tauCoeffWeightedSum lam))

theorem fourierPPrime_mul_tauAbel_abs_bound {lam μ α : ℝ}
    (hlam : 0 < lam) (hμ : 0 < μ) (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α * tauAbel lam μ α| ≤ fourierTauProductControl lam := by
  have h1 := fourierPPrime_alpha_bound hlam hα
  have h2 := sawS_abs_le_two_mul_abs hμ α
  have h3 := tauAbelCorrection_abs_bound (α := α) hlam hμ
  have : 0 ≤ tauCoeffWeightedSum lam := tsum_nonneg fun n => by positivity
  have h4 := abs_add_le ((1 / (2 * π)) * Bethe.sawS μ α) (∑' n, tauAbelCorrectionTerm lam μ α n)
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))] at h4
  have h5 : |tauAbel lam μ α| ≤ 1 / (2 * π) * (2 + tauCoeffWeightedSum lam) * |α| := by
    rw [tauAbel_eq_sawS_add_correction hlam hμ]
    nlinarith [(by positivity : (0 : ℝ) < 1 / (2 * π))]
  rw [abs_mul, fourierTauProductControl]
  nlinarith [abs_nonneg (fourierPPrime lam α), (by positivity : (0 : ℝ) ≤ 1 / (2 * π) * (2 + tauCoeffWeightedSum lam))]

theorem abel_tendsto {f : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => ∑' n, f n * Real.exp (-(1 / ((N : ℝ) + 1))) ^ (n + 1)) atTop (𝓝 L) := by
  have hr0 : Tendsto (fun N : ℕ => Real.exp (-(1 / ((N : ℝ) + 1)))) atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
    rw [neg_zero] at this
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp this
  have := hr0.mul ((Real.tendsto_tsum_powerSeries_nhdsWithin_lt h).comp
    (tendsto_nhdsWithin_iff.2 ⟨hr0, .of_forall fun N => by simp; positivity⟩))
  simp only [one_mul] at this
  refine this.congr fun N => ?_
  simp only [Function.comp_apply, ← tsum_mul_left]
  exact tsum_congr fun n => by ring

theorem tauFourierTerm_abs_bound (lam α : ℝ) (n : ℕ) :
    |tauFourierTerm lam α n| ≤ |α| / π := by
  rw [tauFourierTerm, abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos pi_pos,
    abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
  calc _ ≤ 1 / (π * ((n : ℝ) + 1)) * 1 * (((n : ℝ) + 1) * |α|) := by
        gcongr
        · simp
        · exact (Real.abs_tanh_lt_one _).le
        · exact abs_sin_succ_le n α
    _ = |α| / π := by field_simp

theorem mem_Icc_of_uIoc {α : ℝ} (hα : α ∈ uIoc (-π) π) : α ∈ Icc (-π) π := by
  simp [uIoc_of_le (neg_le_self Real.pi_nonneg)] at hα
  grind

def tauCorrectionTerm (lam : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) *
    Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) *
      (Real.exp (-2 * lam * ((n + 1 : ℕ) : ℝ)) - 1)

section
variable {lam μ : ℝ} (hlam : 0 < lam)
include hlam
theorem tauAbel_integral_term (n : ℕ) :
    ∫ α in (-π)..π,
        fourierPPrime lam α * tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1) =
      tauCorrectionTerm lam n * Real.exp (-μ) ^ (n + 1) := by
  rw [tauCorrectionTerm, ← fourierP_prime_sine_integral hlam (n + 1) n.succ_pos,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_mul_const]
  congr 1
  funext α
  simp only [tauFourierTerm]
  field_simp

theorem fourierPPrime_tauAbel_integral (hμ : 0 < μ) :
    ∫ α in (-π)..π, fourierPPrime lam α * tauAbel lam μ α =
      ∑' n : ℕ, tauCorrectionTerm lam n * Real.exp (-μ) ^ (n + 1) := by
  have hgeo : Summable (fun n : ℕ => Real.exp (-μ) ^ (n + 1)) := by
    simpa [pow_succ] using (summable_geometric_of_lt_one (by positivity)
      (by simp_all : Real.exp (-μ) < 1)).mul_right (Real.exp (-μ))
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun n α => fourierPPrime lam α * tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1))
    (f := fun α => fourierPPrime lam α * tauAbel lam μ α)
    (fun n α => (fourierPrimeControl lam / π) * Real.exp (-μ) ^ (n + 1))
    (fun n => (((measurable_fourierPPrime lam).mul (by unfold tauFourierTerm; fun_prop)).mul
      measurable_const).aestronglyMeasurable)
    (fun n => .of_forall fun α hα => by
      have h1 := fourierPPrime_alpha_bound hlam (mem_Icc_of_uIoc hα)
      have h2 := (le_div_iff₀ pi_pos).1 (tauFourierTerm_abs_bound lam α n)
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, Real.abs_exp]
      gcongr
      rw [le_div_iff₀ pi_pos]
      nlinarith [abs_nonneg (fourierPPrime lam α)])
    (.of_forall fun α _ => hgeo.mul_left _) intervalIntegrable_const
    (.of_forall fun α _ => by
      simpa [tauAbel_eq_sawS_add_correction hlam hμ, mul_assoc] using
        (hasSum_tauAbel hlam hμ α).mul_left (fourierPPrime lam α))
  rw [← hsum.tsum_eq]
  exact tsum_congr fun n => tauAbel_integral_term hlam n

/-- The `α`-coordinate value of the explicit series integral in §4.  The correction series is
interpreted by its ordered partial sums; Abel damping identifies the integral with that limit. -/
theorem fourierPPrime_tauSeries_integral  :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (logCoshTauCorrectionPartial lam) atTop
        (𝓝 (∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α)) := by
  obtain ⟨S, hS, hid⟩ := identity43 lam hlam
  have hC := (tendsto_const_nhds (x := Real.log (Real.cosh lam))).sub hid
  simp only [sub_sub_cancel] at hC
  have hpartial : ∀ N, ∑ n ∈ Finset.range N, tauCorrectionTerm lam n =
      logCoshTauCorrectionPartial lam N := by
    intro N
    induction N <;> simp_all [Finset.sum_range_succ, Finset.sum_Icc_succ_top,
      logCoshTauCorrectionPartial, tauCorrectionTerm, mul_comm]
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume)
    (F := fun (N : ℕ) α => fourierPPrime lam α * tauAbel lam (1 / ((N : ℝ) + 1)) α)
    (f := fun α => fourierPPrime lam α * Bethe.tauSeries lam α)
    (fun _ : ℝ => fourierTauProductControl lam)
    (.of_forall fun N => ((measurable_fourierPPrime lam).mul
      (continuous_tauAbel hlam (by positivity)).measurable).aestronglyMeasurable)
    (.of_forall fun N => .of_forall fun α hα =>
      fourierPPrime_mul_tauAbel_abs_bound hlam (by positivity) (mem_Icc_of_uIoc hα))
    intervalIntegrable_const (by
      filter_upwards [Measure.ae_ne volume π] with α hαπ hα
      have := mem_Icc_of_uIoc hα
      have hαabs : |α| < π := by grind
      exact tendsto_const_nhds.mul (abel_tendsto
        (by rw [Bethe.tauSeries_eq hlam hαabs]; exact Bethe.tendsto_tauPartial hlam hαabs)))
  refine ⟨S, hS, ?_⟩
  rwa [tendsto_nhds_unique (hDCT.congr fun N => fourierPPrime_tauAbel_integral hlam (by positivity))
    (abel_tendsto (hC.congr fun N => (hpartial N).symm))]
end

end PottsDiscontinuity
