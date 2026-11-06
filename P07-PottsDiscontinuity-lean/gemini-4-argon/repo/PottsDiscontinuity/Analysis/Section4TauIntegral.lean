module

public import Mathlib
public import PottsDiscontinuity.Analysis.Section4Series

@[expose] public section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

noncomputable def fourierPrimeControl (lam : ℝ) : ℝ :=
  (π / (Real.cosh (2 * lam) - 1) + π ^ 2 / 2) / 2

private theorem fourierPPrime_alpha_bound {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α| * |α| ≤ fourierPrimeControl lam := by
  have hcosh : 1 < Real.cosh (2 * lam) := Real.one_lt_cosh.mpr (by positivity)
  by_cases hα0 : α = 0
  · simp [fourierPPrime, hα0, fourierPrimeControl]; positivity
  · have hcosLower := fourier_one_sub_cos_lower hα
    have hαabs : |α| ≤ π := abs_le.mpr ⟨by linarith [hα.1], hα.2⟩
    have hαsq : 0 < α ^ 2 := sq_pos_of_ne_zero hα0
    have hdenLower : 0 < 1 - Real.cos α := lt_of_lt_of_le (by positivity) hcosLower
    have hden1 : 0 < Real.cosh (2 * lam) - Real.cos α := by linarith [Real.cos_le_one α]
    have hden1Lower : Real.cosh (2 * lam) - 1 ≤ Real.cosh (2 * lam) - Real.cos α := by
      linarith [Real.cos_le_one α]
    have hcoshden : 0 < Real.cosh (2 * lam) - 1 := by linarith
    have hfirst :
        |Real.sin α| * |α| / (Real.cosh (2 * lam) - Real.cos α) ≤
          π / (Real.cosh (2 * lam) - 1) := by
      have hnum : |Real.sin α| * |α| ≤ π := by
        nlinarith [Real.abs_sin_le_one α, abs_nonneg α]
      exact (div_le_div_of_nonneg_left (by positivity) hcoshden hden1Lower).trans
        (div_le_div_of_nonneg_right hnum hcoshden.le)
    have hsecond : |Real.sin α| * |α| / (1 - Real.cos α) ≤ π ^ 2 / 2 := by
      rw [div_le_iff₀ hdenLower]
      have h1 : |Real.sin α| * |α| ≤ α ^ 2 := by
        nlinarith [Real.abs_sin_le_abs (x := α), sq_abs α, abs_nonneg α]
      have h2 : α ^ 2 ≤ (π ^ 2 / 2) * (1 - Real.cos α) := by
        have := mul_le_mul_of_nonneg_left hcosLower (by positivity : (0 : ℝ) ≤ π ^ 2 / 2)
        rwa [show (π ^ 2 / 2) * (2 * α ^ 2 / π ^ 2) = α ^ 2 by
          field_simp [Real.pi_ne_zero]] at this
      exact h1.trans h2
    simp only [fourierPPrime, hα0, ↓reduceIte, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc
      (1 / 2 : ℝ) *
          |Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
            Real.sin α / (1 - Real.cos α)| * |α| ≤
        (1 / 2 : ℝ) *
          (|Real.sin α| * |α| / (Real.cosh (2 * lam) - Real.cos α) +
            |Real.sin α| * |α| / (1 - Real.cos α)) := by
        have hab := abs_sub (Real.sin α / (Real.cosh (2 * lam) - Real.cos α))
          (Real.sin α / (1 - Real.cos α))
        rw [abs_div, abs_div, abs_of_pos hden1, abs_of_pos hdenLower] at hab
        have hmul := mul_le_mul_of_nonneg_right hab (abs_nonneg α)
        rw [add_mul, div_mul_eq_mul_div, div_mul_eq_mul_div] at hmul
        linarith
      _ ≤ fourierPrimeControl lam := by
        dsimp [fourierPrimeControl]; linarith

noncomputable def tauFourierTerm (lam α : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / (π * ((n : ℝ) + 1)) *
    Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) * Real.sin (((n + 1 : ℕ) : ℝ) * α)

noncomputable def tauAbel (lam μ α : ℝ) : ℝ :=
  ∑' n : ℕ, tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1)

noncomputable def tauAbelCorrectionTerm (lam μ α : ℝ) (n : ℕ) : ℝ :=
  (1 / (2 * π) : ℝ) * Real.exp (-μ) ^ (n + 1) *
    Bethe.tauCoeff lam n * Real.sin (((n + 1 : ℕ) : ℝ) * α)

private theorem tauAbelCorrectionTerm_norm_le {lam μ α : ℝ} (hμ : 0 < μ) (n : ℕ) :
    ‖tauAbelCorrectionTerm lam μ α n‖ ≤ |Bethe.tauCoeff lam n| / (2 * π) := by
  rw [Real.norm_eq_abs, tauAbelCorrectionTerm, abs_mul, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π)),
    abs_of_nonneg (by positivity : 0 ≤ Real.exp (-μ) ^ (n + 1))]
  have hpow : Real.exp (-μ) ^ (n + 1) ≤ 1 :=
    pow_le_one₀ (Real.exp_pos _).le (by rw [Real.exp_le_one_iff]; linarith)
  have hsin := Real.abs_sin_le_one (((n + 1 : ℕ) : ℝ) * α)
  have h1 : Real.exp (-μ) ^ (n + 1) * |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤ 1 := by
    nlinarith [abs_nonneg (Real.sin (((n + 1 : ℕ) : ℝ) * α))]
  calc (1 / (2 * π)) * Real.exp (-μ) ^ (n + 1) * |Bethe.tauCoeff lam n| *
        |Real.sin (((n + 1 : ℕ) : ℝ) * α)|
    _ = (|Bethe.tauCoeff lam n| / (2 * π)) *
        (Real.exp (-μ) ^ (n + 1) * |Real.sin (((n + 1 : ℕ) : ℝ) * α)|) := by ring
    _ ≤ (|Bethe.tauCoeff lam n| / (2 * π)) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = |Bethe.tauCoeff lam n| / (2 * π) := mul_one _

private theorem summable_tauAbelCorrection {lam μ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (α : ℝ) : Summable (tauAbelCorrectionTerm lam μ α) :=
  Summable.of_norm_bounded ((Bethe.summable_tauCoeff hlam).abs.div_const (2 * π))
    (tauAbelCorrectionTerm_norm_le hμ)

private theorem tauAbel_eq_sawS_add_correction {lam μ α : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) :
    tauAbel lam μ α = (1 / (2 * π) : ℝ) * Bethe.sawS μ α +
      ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n := by
  let r : ℝ := Real.exp (-μ)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by dsimp [r]; rw [Real.exp_lt_one_iff]; linarith
  have hbase : Summable (fun n : ℕ =>
      2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) *
        Real.sin (((n + 1 : ℕ) : ℝ) * α)) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => 2 * r ^ (n + 1))
    · exact ((summable_geometric_of_lt_one hr.le hr1).mul_left (2 * r)).congr
        fun n => by rw [pow_succ]; ring
    · intro n
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hrpow : 0 ≤ r ^ (n + 1) := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one,
        one_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hrpow, abs_of_pos hn0, mul_one]
      calc 2 * r ^ (n + 1) / ((n : ℝ) + 1) * |Real.sin (((n + 1 : ℕ) : ℝ) * α)|
        _ ≤ 2 * r ^ (n + 1) / ((n : ℝ) + 1) * 1 := by
          gcongr; exact Real.abs_sin_le_one _
        _ ≤ 2 * r ^ (n + 1) := by
          simpa using div_le_self (by positivity : 0 ≤ 2 * r ^ (n + 1)) hn
  have hcorr := summable_tauAbelCorrection hlam hμ α
  have hterm (n : ℕ) :
      tauFourierTerm lam α n * r ^ (n + 1) =
        (1 / (2 * π) : ℝ) *
          (2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) *
            Real.sin (((n + 1 : ℕ) : ℝ) * α)) +
        tauAbelCorrectionTerm lam μ α n := by
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [tauFourierTerm, tauAbelCorrectionTerm, Bethe.tauCoeff,
      show lam * ((n + 1 : ℕ) : ℝ) = lam * ((n : ℝ) + 1) by push_cast; ring, pow_succ (-1 : ℝ)]
    field_simp [Real.pi_ne_zero, hn]; ring
  unfold tauAbel Bethe.sawS
  simp only [r, hterm, (hbase.mul_left (1 / (2 * π) : ℝ)).tsum_add hcorr, tsum_mul_left]

private theorem summable_tauCoeff_weighted {lam : ℝ} (hlam : 0 < lam) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * |Bethe.tauCoeff lam n|) := by
  let r : ℝ := Real.exp (-lam)
  have hr : 0 < r := Real.exp_pos _
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr]; dsimp [r]; rw [Real.exp_lt_one_iff]; linarith
  have hpoly : Summable (fun n : ℕ => (n : ℝ) * r ^ n) :=
    summable_norm_iff.mp (by simpa using summable_norm_pow_mul_geometric_of_norm_lt_one (k := 1) hrnorm)
  have hgeom : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ (n + 1)) := by
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hpoly
  refine Summable.of_norm_bounded (hgeom.mul_left 2) fun n => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ((n : ℝ) + 1) * |Bethe.tauCoeff lam n|
    _ ≤ ((n : ℝ) + 1) * (2 * r ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left (Bethe.abs_tauCoeff_le lam n) (by positivity)
    _ = 2 * (((n : ℝ) + 1) * r ^ (n + 1)) := by ring

noncomputable def tauCoeffWeightedSum (lam : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) * |Bethe.tauCoeff lam n|

private theorem tauAbelCorrection_abs_bound {lam μ α : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) :
    |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| ≤
      (1 / (2 * π) : ℝ) * |α| * tauCoeffWeightedSum lam := by
  let c : ℝ := 1 / (2 * π)
  have hc : 0 < c := by positivity
  have hcorr := (summable_tauAbelCorrection hlam hμ α).norm
  have hmajor := (summable_tauCoeff_weighted hlam).mul_left (c * |α|)
  have hbound (n : ℕ) :
      ‖tauAbelCorrectionTerm lam μ α n‖ ≤
        c * |α| * (((n : ℝ) + 1) * |Bethe.tauCoeff lam n|) := by
    rw [Real.norm_eq_abs, tauAbelCorrectionTerm, abs_mul, abs_mul, abs_mul,
      abs_of_pos hc, abs_of_nonneg (by positivity : 0 ≤ Real.exp (-μ) ^ (n + 1))]
    have hpow : Real.exp (-μ) ^ (n + 1) ≤ 1 :=
      pow_le_one₀ (Real.exp_pos _).le (by rw [Real.exp_le_one_iff]; linarith)
    have hsin : |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤ ((n : ℝ) + 1) * |α| := by
      refine Real.abs_sin_le_abs.trans ?_
      rw [abs_mul, abs_of_nonneg (by positivity)]; push_cast; rfl
    calc c * Real.exp (-μ) ^ (n + 1) * |Bethe.tauCoeff lam n| *
          |Real.sin (((n + 1 : ℕ) : ℝ) * α)|
      _ ≤ c * 1 * |Bethe.tauCoeff lam n| * (((n : ℝ) + 1) * |α|) := by
        gcongr
      _ = c * |α| * (((n : ℝ) + 1) * |Bethe.tauCoeff lam n|) := by ring
  calc |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n|
    _ ≤ ∑' n : ℕ, ‖tauAbelCorrectionTerm lam μ α n‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hcorr
    _ ≤ ∑' n : ℕ, c * |α| * (((n : ℝ) + 1) * |Bethe.tauCoeff lam n|) :=
      hcorr.tsum_le_tsum hbound hmajor
    _ = c * |α| * tauCoeffWeightedSum lam := tsum_mul_left

private theorem sawS_abs_le_two_mul_abs {μ α : ℝ} (hμ : 0 < μ) :
    |Bethe.sawS μ α| ≤ 2 * |α| := by
  rw [Bethe.sawS_eq_arctan hμ α, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
  by_cases hα : |α| ≤ π / 2
  · have hcos : 0 ≤ Real.cos α := Real.cos_nonneg_of_mem_Icc (abs_le.mp hα)
    have hden : 1 ≤ Real.exp μ + Real.cos α := by linarith [Real.one_lt_exp_iff.mpr hμ]
    have hdenPos : 0 < Real.exp μ + Real.cos α := by linarith
    have h1 : |Real.arctan (Real.sin α / (Real.exp μ + Real.cos α))| ≤ |α| :=
      Real.abs_arctan_le_abs.trans <| by
        rw [abs_div, abs_of_pos hdenPos]
        exact (div_le_self (abs_nonneg _) hden).trans Real.abs_sin_le_abs
    linarith
  · have h1 : |Real.arctan (Real.sin α / (Real.exp μ + Real.cos α))| ≤ π / 2 :=
      abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
    linarith

private theorem continuous_tauAbel {lam μ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ) :
    Continuous (tauAbel lam μ) := by
  have hsaw : Continuous (Bethe.sawS μ) :=
    continuous_iff_continuousAt.mpr fun α => (Bethe.hasDerivAt_sawS hμ α).continuousAt
  have hcorr : Continuous (fun α => ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n) :=
    continuous_tsum (fun n => by unfold tauAbelCorrectionTerm; fun_prop)
      ((Bethe.summable_tauCoeff hlam).abs.div_const (2 * π))
      (fun n α => tauAbelCorrectionTerm_norm_le hμ n)
  have heq : tauAbel lam μ = fun α =>
      (1 / (2 * π) : ℝ) * Bethe.sawS μ α + ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n :=
    funext fun _ => tauAbel_eq_sawS_add_correction hlam hμ
  rw [heq]
  exact (continuous_const.mul hsaw).add hcorr

private theorem measurable_fourierPPrime (lam : ℝ) :
    Measurable (fourierPPrime lam) := by
  unfold fourierPPrime
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

noncomputable def tauLocalControl (lam : ℝ) : ℝ :=
  1 / π + (1 / (2 * π)) * tauCoeffWeightedSum lam

private theorem tauLocalControl_nonneg {lam : ℝ} :
    0 ≤ tauLocalControl lam := by
  have hW : 0 ≤ tauCoeffWeightedSum lam := tsum_nonneg fun _ => by positivity
  dsimp [tauLocalControl]; positivity

private theorem tauAbel_local_abs_bound {lam μ α : ℝ} (hlam : 0 < lam) (hμ : 0 < μ) :
    |tauAbel lam μ α| ≤ tauLocalControl lam * |α| := by
  let c : ℝ := 1 / (2 * π)
  have hc : 0 < c := by positivity
  rw [tauAbel_eq_sawS_add_correction hlam hμ]
  calc |c * Bethe.sawS μ α + ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n|
    _ ≤ |c * Bethe.sawS μ α| + |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| := abs_add_le _ _
    _ ≤ c * (2 * |α|) + c * |α| * tauCoeffWeightedSum lam := by
      rw [abs_mul, abs_of_pos hc]
      exact add_le_add (mul_le_mul_of_nonneg_left (sawS_abs_le_two_mul_abs hμ) hc.le)
        (tauAbelCorrection_abs_bound hlam hμ)
    _ = tauLocalControl lam * |α| := by
      dsimp [tauLocalControl, c]; field_simp [Real.pi_ne_zero]

noncomputable def fourierTauProductControl (lam : ℝ) : ℝ :=
  fourierPrimeControl lam * tauLocalControl lam

theorem fourierTauProductControl_nonneg {lam : ℝ} (hlam : 0 < lam) :
    0 ≤ fourierTauProductControl lam := by
  have hcosh : 1 < Real.cosh (2 * lam) := Real.one_lt_cosh.mpr (by positivity)
  have hprime : 0 < fourierPrimeControl lam := by dsimp [fourierPrimeControl]; positivity
  have hlocal := tauLocalControl_nonneg (lam := lam)
  dsimp [fourierTauProductControl]; positivity

private theorem fourierPPrime_mul_tauAbel_abs_bound {lam μ α : ℝ}
    (hlam : 0 < lam) (hμ : 0 < μ) (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α * tauAbel lam μ α| ≤ fourierTauProductControl lam := by
  rw [abs_mul]
  calc |fourierPPrime lam α| * |tauAbel lam μ α|
    _ ≤ |fourierPPrime lam α| * (tauLocalControl lam * |α|) :=
      mul_le_mul_of_nonneg_left (tauAbel_local_abs_bound hlam hμ) (abs_nonneg _)
    _ = (|fourierPPrime lam α| * |α|) * tauLocalControl lam := by ring
    _ ≤ fourierTauProductControl lam :=
      mul_le_mul_of_nonneg_right (fourierPPrime_alpha_bound hlam hα) tauLocalControl_nonneg

private theorem tendsto_abel_exp_seq {f : ℕ → ℝ} {L : ℝ}
    (hpartial : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => ∑' n : ℕ, f n * Real.exp (-(1 / ((N : ℝ) + 1))) ^ (n + 1))
      atTop (𝓝 L) := by
  let r : ℕ → ℝ := fun N => Real.exp (-(1 / ((N : ℝ) + 1)))
  have hsmall : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hneg : Tendsto (fun N : ℕ => -(1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using hsmall.neg
  have hr0 : Tendsto r atTop (𝓝 1) := by
    simpa only [r, Function.comp_def, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp hneg
  have hr : Tendsto r atTop (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr0, Filter.Eventually.of_forall fun N => by
      simp only [Set.mem_Iio, r, Real.exp_lt_one_iff]
      linarith [show 0 < 1 / ((N : ℝ) + 1) by positivity]⟩
  have hmul := hr0.mul ((Real.tendsto_tsum_powerSeries_nhdsWithin_lt hpartial).comp hr)
  rw [one_mul] at hmul
  refine hmul.congr fun N => ?_
  dsimp [Function.comp_def]
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by dsimp [r]; rw [pow_succ]; ring

noncomputable def tauAbelSeq (lam α : ℝ) (N : ℕ) : ℝ :=
  tauAbel lam (1 / ((N : ℝ) + 1)) α

private theorem tauAbelSeq_tendsto_tauSeries {lam α : ℝ} (hlam : 0 < lam)
    (hα : |α| < π) : Tendsto (tauAbelSeq lam α) atTop (𝓝 (Bethe.tauSeries lam α)) := by
  have h := Bethe.tendsto_tauPartial hlam hα
  rw [← Bethe.tauSeries_eq hlam hα] at h
  exact tendsto_abel_exp_seq h

theorem fourierPPrime_tauSeries_abs_bound {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α * Bethe.tauSeries lam α| ≤ fourierTauProductControl lam := by
  by_cases hαp : α = π
  · subst α; simp [Bethe.tauSeries_pi, fourierTauProductControl_nonneg hlam]
  by_cases hαm : α = -π
  · subst α; simp [Bethe.tauSeries_neg_pi, fourierTauProductControl_nonneg hlam]
  have hαabs : |α| < π := abs_lt.mpr
    ⟨lt_of_le_of_ne hα.1 (Ne.symm hαm), lt_of_le_of_ne hα.2 hαp⟩
  have hprod : Tendsto
      (fun N : ℕ => |fourierPPrime lam α * tauAbelSeq lam α N|) atTop
      (𝓝 |fourierPPrime lam α * Bethe.tauSeries lam α|) := by
    simpa only [Real.norm_eq_abs] using
      (tendsto_const_nhds.mul (tauAbelSeq_tendsto_tauSeries hlam hαabs)).norm
  exact le_of_tendsto_of_tendsto' hprod tendsto_const_nhds fun N =>
    fourierPPrime_mul_tauAbel_abs_bound hlam (by positivity) hα

private theorem tauFourierTerm_abs_bound (lam α : ℝ) (n : ℕ) :
    |tauFourierTerm lam α n| ≤ |α| / π := by
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have hsin : |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤ ((n : ℝ) + 1) * |α| := by
    refine Real.abs_sin_le_abs.trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity)]; push_cast; rfl
  rw [tauFourierTerm, abs_mul, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (mul_pos Real.pi_pos hm)]
  calc 1 / (π * ((n : ℝ) + 1)) * |Real.tanh (lam * ((n + 1 : ℕ) : ℝ))| *
        |Real.sin (((n + 1 : ℕ) : ℝ) * α)|
    _ ≤ 1 / (π * ((n : ℝ) + 1)) * 1 * (((n : ℝ) + 1) * |α|) := by
      gcongr; exact (Real.abs_tanh_lt_one _).le
    _ = |α| / π := by field_simp [Real.pi_ne_zero]

private theorem hasSum_tauAbelTerms {lam μ α : ℝ} (hμ : 0 < μ) :
    HasSum (fun n : ℕ => tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1))
      (tauAbel lam μ α) := by
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hr1 : Real.exp (-μ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hgeo : Summable (fun n : ℕ => Real.exp (-μ) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hr.le hr1).mul_left (Real.exp (-μ))).congr
      fun n => by rw [pow_succ]; ring
  refine (Summable.of_norm_bounded (hgeo.mul_left (|α| / π)) fun n => ?_).hasSum
  have hpow : 0 ≤ Real.exp (-μ) ^ (n + 1) := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow]
  exact mul_le_mul_of_nonneg_right (tauFourierTerm_abs_bound lam α n) hpow

noncomputable def tauCorrectionTerm (lam : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) *
    Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) *
      (Real.exp (-2 * lam * ((n + 1 : ℕ) : ℝ)) - 1)

private theorem tauAbel_integral_term {lam μ : ℝ} (hlam : 0 < lam) (n : ℕ) :
    ∫ α in (-π)..π,
        fourierPPrime lam α * tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1) =
      tauCorrectionTerm lam n * Real.exp (-μ) ^ (n + 1) := by
  have hsine := fourierP_prime_sine_integral hlam (n + 1) (Nat.succ_pos n)
  have hsine' :
      ∫ α in (-π)..π, fourierPPrime lam α * Real.sin (((n + 1 : ℕ) : ℝ) * α) =
        π * (Real.exp (-2 * lam * ((n + 1 : ℕ) : ℝ)) - 1) := by
    rw [← hsine]; field_simp [Real.pi_ne_zero]
  have hfun :
      (fun α : ℝ => fourierPPrime lam α * tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1)) =
        fun α =>
          (Real.exp (-μ) ^ (n + 1) *
            ((-1 : ℝ) ^ (n + 1) / (π * ((n : ℝ) + 1)) *
              Real.tanh (lam * ((n + 1 : ℕ) : ℝ)))) *
            (fourierPPrime lam α * Real.sin (((n + 1 : ℕ) : ℝ) * α)) := by
    funext α; simp [tauFourierTerm]; ring
  rw [hfun, intervalIntegral.integral_const_mul, hsine', tauCorrectionTerm]
  have hmne : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [Real.pi_ne_zero, hmne]

private theorem fourierPPrime_tauAbel_integral {lam μ : ℝ}
    (hlam : 0 < lam) (hμ : 0 < μ) :
    ∫ α in (-π)..π, fourierPPrime lam α * tauAbel lam μ α =
      ∑' n : ℕ, tauCorrectionTerm lam n * Real.exp (-μ) ^ (n + 1) := by
  let r : ℝ := Real.exp (-μ)
  let B : ℕ → ℝ := fun n => (fourierPrimeControl lam / π) * r ^ (n + 1)
  let F : ℕ → ℝ → ℝ := fun n α =>
    fourierPPrime lam α * tauFourierTerm lam α n * r ^ (n + 1)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by dsimp [r]; rw [Real.exp_lt_one_iff]; linarith
  have hB : Summable B :=
    (((summable_geometric_of_lt_one hr.le hr1).mul_left r).congr
      fun n => by rw [pow_succ]; ring).mul_left (fourierPrimeControl lam / π)
  have hmeas (n : ℕ) :
      AEStronglyMeasurable (F n) (volume.restrict (uIoc (-π) π)) :=
    ((measurable_fourierPPrime lam).mul (by unfold tauFourierTerm; fun_prop) |>.mul
      measurable_const).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ α ∂volume, α ∈ uIoc (-π) π → ‖F n α‖ ≤ B n := by
    filter_upwards with α hα
    have hαIoc : α ∈ Ioc (-π) π := by
      simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
    have hP := fourierPPrime_alpha_bound hlam (Ioc_subset_Icc_self hαIoc)
    have hterm := tauFourierTerm_abs_bound lam α n
    have hcoeff :
        |fourierPPrime lam α| * |tauFourierTerm lam α n| ≤ fourierPrimeControl lam / π := by
      calc |fourierPPrime lam α| * |tauFourierTerm lam α n|
        _ ≤ |fourierPPrime lam α| * (|α| / π) :=
          mul_le_mul_of_nonneg_left hterm (abs_nonneg _)
        _ = (|fourierPPrime lam α| * |α|) / π := by ring
        _ ≤ fourierPrimeControl lam / π :=
          div_le_div_of_nonneg_right hP Real.pi_pos.le
    have hpow : 0 ≤ r ^ (n + 1) := by positivity
    change ‖fourierPPrime lam α * tauFourierTerm lam α n * r ^ (n + 1)‖ ≤
      (fourierPrimeControl lam / π) * r ^ (n + 1)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hpow]
    exact mul_le_mul_of_nonneg_right hcoeff hpow
  have hlim : ∀ᵐ α ∂volume, α ∈ uIoc (-π) π →
      HasSum (fun n : ℕ => F n α) (fourierPPrime lam α * tauAbel lam μ α) :=
    Filter.Eventually.of_forall fun α _ =>
      ((hasSum_tauAbelTerms hμ).mul_left (fourierPPrime lam α)).congr_fun
        fun n => by simp [F, r]; ring
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -π) (b := π) (F := F)
    (f := fun α => fourierPPrime lam α * tauAbel lam μ α)
    (fun n _ => B n) hmeas hbound
    (Filter.Eventually.of_forall fun _ _ => hB) intervalIntegrable_const hlim
  rw [← hsum.tsum_eq]
  exact tsum_congr fun n => tauAbel_integral_term hlam n

noncomputable def tauCorrectionPartial (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, tauCorrectionTerm lam n

private theorem tauCorrectionPartial_eq (lam : ℝ) (N : ℕ) :
    tauCorrectionPartial lam N = logCoshTauCorrectionPartial lam N := by
  unfold tauCorrectionPartial logCoshTauCorrectionPartial
  rw [sum_Icc_one_eq_sum_range]
  refine Finset.sum_congr rfl fun n _ => ?_
  dsimp [tauCorrectionTerm]; push_cast; ring_nf

noncomputable def tauCorrectionAbelSeq (lam : ℝ) (N : ℕ) : ℝ :=
  ∑' n : ℕ, tauCorrectionTerm lam n * Real.exp (-(1 / ((N : ℝ) + 1))) ^ (n + 1)

theorem fourierPPrime_tauSeries_integral {lam : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (logCoshTauCorrectionPartial lam) atTop
        (𝓝 (∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α)) := by
  obtain ⟨S, hS, hidentity⟩ := identity43 lam hlam
  have hCorr : Tendsto (logCoshTauCorrectionPartial lam) atTop
      (𝓝 (Real.log (Real.cosh lam) - (lam + 2 * S))) :=
    (tendsto_const_nhds.sub hidentity).congr' (Filter.Eventually.of_forall fun _ => by ring)
  have hPartialCorr : Tendsto (tauCorrectionPartial lam) atTop
      (𝓝 (Real.log (Real.cosh lam) - (lam + 2 * S))) :=
    hCorr.congr' (Filter.Eventually.of_forall fun N => (tauCorrectionPartial_eq lam N).symm)
  have hAbelCorr : Tendsto (tauCorrectionAbelSeq lam) atTop
      (𝓝 (Real.log (Real.cosh lam) - (lam + 2 * S))) :=
    tendsto_abel_exp_seq hPartialCorr
  let F : ℕ → ℝ → ℝ := fun N α => fourierPPrime lam α * tauAbelSeq lam α N
  have hmeas (N : ℕ) : AEStronglyMeasurable (F N) (volume.restrict (uIoc (-π) π)) :=
    ((measurable_fourierPPrime lam).mul
      (continuous_tauAbel hlam (by positivity)).measurable).aestronglyMeasurable
  have hbound (N : ℕ) : ∀ᵐ α ∂volume, α ∈ uIoc (-π) π →
      ‖F N α‖ ≤ fourierTauProductControl lam := by
    filter_upwards with α hα
    have hαIoc : α ∈ Ioc (-π) π := by
      simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
    rw [Real.norm_eq_abs]
    exact fourierPPrime_mul_tauAbel_abs_bound hlam (by positivity) (Ioc_subset_Icc_self hαIoc)
  have hlim : ∀ᵐ α ∂volume, α ∈ uIoc (-π) π →
      Tendsto (fun N : ℕ => F N α) atTop
        (𝓝 (fourierPPrime lam α * Bethe.tauSeries lam α)) := by
    filter_upwards [Measure.ae_ne volume π] with α hαπ hα
    have hαIoc : α ∈ Ioc (-π) π := by
      simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
    have hαabs : |α| < π := abs_lt.mpr ⟨by linarith [hαIoc.1], lt_of_le_of_ne hαIoc.2 hαπ⟩
    simpa [F, tauAbelSeq] using tendsto_const_nhds.mul (tauAbelSeq_tendsto_tauSeries hlam hαabs)
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := -π) (b := π) (F := F)
    (f := fun α => fourierPPrime lam α * Bethe.tauSeries lam α)
    (fun _ : ℝ => fourierTauProductControl lam)
    (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall hbound)
    intervalIntegrable_const hlim
  have hDCT' : Tendsto (tauCorrectionAbelSeq lam) atTop
      (𝓝 (∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α)) :=
    hDCT.congr fun N => fourierPPrime_tauAbel_integral hlam (by positivity)
  rw [← tendsto_nhds_unique hDCT' hAbelCorr] at hCorr
  exact ⟨S, hS, hCorr⟩

end PottsDiscontinuity
