module

public import ThreeSumApsp.Sec4.ChoosingParameters

@[expose] public section

namespace ThreeSumApsp

noncomputable def logTwoLo : ℝ := 0.6931471803
noncomputable def logTwoHi : ℝ := 0.6931471808
noncomputable def logThreeHi : ℝ := 1.0986122892

noncomputable def seriesArg (k : ℤ) (θ : ℝ) : ℝ := (θ - 2 ^ k) / (θ + 2 ^ k)

noncomputable def logApprox (k : ℤ) (n : ℕ) (θ : ℝ) : ℝ :=
  k * ((logTwoLo + logTwoHi) / 2)
    + 2 * ∑ i ∈ Finset.range n, seriesArg k θ ^ (2 * i + 1) / (2 * i + 1)

noncomputable def logErr (k : ℤ) (n : ℕ) (θ : ℝ) : ℝ :=
  |(k : ℝ)| * ((logTwoHi - logTwoLo) / 2) + 2 * (seriesArg k θ ^ (2 * n) / (1 - seriesArg k θ ^ 2))

noncomputable def logLo (k : ℤ) (x : ℝ) : ℝ := logApprox k 4 x - logErr k 4 x
noncomputable def logHi (k : ℤ) (x : ℝ) : ℝ := logApprox k 4 x + logErr k 4 x

macro "numerics" : tactic =>
  `(tactic| norm_num [logLo, logHi, logApprox, logErr, seriesArg, logTwoLo, logTwoHi, logThreeHi,
    Finset.sum_range_succ])

theorem log_two_mem : Real.log 2 ∈ Set.Icc logTwoLo logTwoHi :=
  ⟨Real.log_two_gt_d9.le, Real.log_two_lt_d9.le⟩

theorem logFour_mem : Real.log 4 ∈ Set.Icc (2 * logTwoLo) (2 * logTwoHi) := by
  rw [Real.log_four]
  exact ⟨by linarith [log_two_mem.1], by linarith [log_two_mem.2]⟩

theorem log_mem (k : ℤ) (n : ℕ) {θ : ℝ} (hθ : 0 < θ := by numerics) :
    Real.log θ ∈ Set.Icc (logApprox k n θ - logErr k n θ) (logApprox k n θ + logErr k n θ) := by
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hx : |seriesArg k θ| < 1 := by
    rw [seriesArg, abs_div, abs_of_pos (add_pos hθ hpow), div_lt_one (add_pos hθ hpow), abs_lt]
    constructor <;> linarith
  have hsq : 0 < 1 - seriesArg k θ ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one _).2 hx)
  have hlog : Real.log θ
      = k * Real.log 2 + Real.log ((1 + seriesArg k θ) / (1 - seriesArg k θ)) := by
    have hdiv : (1 + seriesArg k θ) / (1 - seriesArg k θ) = θ / 2 ^ k := by
      rw [seriesArg]; field_simp; ring
    rw [hdiv, Real.log_div hθ.ne' hpow.ne', Real.log_zpow]; ring
  have htwo : |k * Real.log 2 - k * ((logTwoLo + logTwoHi) / 2)|
      ≤ |(k : ℝ)| * ((logTwoHi - logTwoLo) / 2) := by
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg _) <;>
      linarith [log_two_mem.1, log_two_mem.2]
  have hseries := (Real.sum_range_sub_log_div_le hx n).trans
    (div_le_div_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg _) hx.le (Nat.le_succ _)) hsq.le)
  rw [(even_two_mul n).pow_abs] at hseries
  rw [abs_le] at htwo hseries
  rw [hlog, logApprox, logErr]
  constructor <;> linarith [htwo.1, htwo.2, hseries.1, hseries.2]

theorem log_three_le : Real.log 3 ≤ logThreeHi :=
  (log_mem 2 7).2.trans (by numerics)

theorem qOf_le (k : ℤ) {θ r : ℝ} (h0 : 0 < θ := by numerics) (h1 : θ < 1 := by numerics)
    (hr : 0 ≤ r := by numerics)
    (h : -θ * logLo k θ - (1 - θ) * logLo 0 (1 - θ) + θ * (2 * logThreeHi)
      ≤ r * (2 * logTwoLo) := by numerics) : qOf θ ≤ r := by
  have hcompl : 0 < 1 - θ := sub_pos.2 h1
  unfold qOf entropy
  unfold logLo at h
  rw [Real.log_four, Real.log_nine, div_le_iff₀ (mul_pos two_pos (Real.log_pos one_lt_two))]
  linarith [h, mul_le_mul_of_nonneg_left (log_mem k 4 h0).1 h0.le,
    mul_le_mul_of_nonneg_left (log_mem 0 4 hcompl).1 hcompl.le,
    mul_le_mul_of_nonneg_left log_three_le h0.le,
    mul_le_mul_of_nonneg_left log_two_mem.1 hr]

end ThreeSumApsp
