/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.ChoosingParameters

/-!
# The numerical toolkit for Table 2

Table 2 and the proof of Corollary 26 evaluate the exponents `q(θ)` and `γ = θ ln(1/ρ_c)/ln 4` of
Corollary 31 and the bound `R_c(γ)` of (11) at rational points. All three are built from logarithms
of rational numbers. This file turns each such claim into inequalities between rational numbers,
which the tactic `numerics` checks by evaluating both sides.

* `log_mem` encloses `log θ`: write `θ = 2^k (1 + x)/(1 - x)` with `2^k` near `θ`, and sum `n` terms
  of `log ((1 + x)/(1 - x)) = 2 (x + x³/3 + x⁵/5 + ⋯)`.
* `qOf_le` and `le_qOf` bound `q(θ)` at a rational `θ`.
* `gammaOf_one_mem`, `lnΛ_zero_mem`, `lt_Rc_of_lnΛ_zero_mem` and `Rc_lt_of_lnΛ_zero_mem` treat the
  two numbers on which a row of the table depends: `ln(1/ρ_c)/ln 4` and the denominator of (11) at
  `γ = 0`.
* `Table2Query.intro`, `Table2Ninth.intro` and `Table2Density.intro` give an entry of the table from
  two rational numbers that enclose its `θ`; the `θ` itself comes from the intermediate value
  theorem.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Logarithms of rational numbers -/

/-- Mathlib's lower bound on `ln 2 = 0.693147180559…`. -/
noncomputable def logTwoLo : ℝ := 0.6931471803

/-- Mathlib's upper bound on `ln 2 = 0.693147180559…`. -/
noncomputable def logTwoHi : ℝ := 0.6931471808

/-- A lower bound on `ln 3 = 1.098612288668…`. -/
noncomputable def logThreeLo : ℝ := 1.0986122881

/-- An upper bound on `ln 3 = 1.098612288668…`. -/
noncomputable def logThreeHi : ℝ := 1.0986122892

/-- A lower bound on `ln 10 = 2.302585092994…`. -/
noncomputable def logTenLo : ℝ := 2.3025850922

/-- An upper bound on `ln 10 = 2.302585092994…`. -/
noncomputable def logTenHi : ℝ := 2.3025850938

/-- The `x` with `θ = 2^k (1 + x)/(1 - x)`. It is small when `2^k` is near `θ`. -/
noncomputable def seriesArg (k : ℤ) (θ : ℝ) : ℝ := (θ - 2 ^ k) / (θ + 2 ^ k)

/-- The approximation `k ln 2 + 2 (x + x³/3 + ⋯)` of `log θ`, with `n` terms of the series at
`x = seriesArg k θ`, and with the midpoint of the two bounds in place of `ln 2`. -/
noncomputable def logApprox (k : ℤ) (n : ℕ) (θ : ℝ) : ℝ :=
  k * ((logTwoLo + logTwoHi) / 2)
    + 2 * ∑ i ∈ Finset.range n, seriesArg k θ ^ (2 * i + 1) / (2 * i + 1)

/-- A bound on the error of `logApprox`: `|k|` times half the distance of the two bounds on `ln 2`,
and the remainder of the series. -/
noncomputable def logErr (k : ℤ) (n : ℕ) (θ : ℝ) : ℝ :=
  |(k : ℝ)| * ((logTwoHi - logTwoLo) / 2) + 2 * (seriesArg k θ ^ (2 * n) / (1 - seriesArg k θ ^ 2))

/-- Proves an equation or inequality between explicit rational numbers by evaluating both sides,
after unfolding the approximations of logarithms. -/
macro "numerics" : tactic =>
  `(tactic| norm_num [logApprox, logErr, seriesArg, logTwoLo, logTwoHi, logThreeLo, logThreeHi,
    logTenLo, logTenHi, Finset.sum_range_succ, rhoC])

private lemma log_two_mem : Real.log 2 ∈ Set.Icc logTwoLo logTwoHi :=
  ⟨Real.log_two_gt_d9.le, Real.log_two_lt_d9.le⟩

/-- The enclosure of `log θ`, between two rational numbers if `θ` is rational. It holds for every
`k` and `n`; they decide only how tight it is. -/
theorem log_mem (k : ℤ) (n : ℕ) {θ : ℝ} (hθ : 0 < θ := by numerics) :
    Real.log θ ∈ Set.Icc (logApprox k n θ - logErr k n θ) (logApprox k n θ + logErr k n θ) := by
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hx : |seriesArg k θ| < 1 := by
    rw [seriesArg, abs_div, abs_of_pos (add_pos hθ hpow), div_lt_one (add_pos hθ hpow), abs_lt]
    constructor <;> linarith
  have hsq := sub_pos.2 ((sq_lt_one_iff_abs_lt_one _).2 hx)
  -- `log θ = k log 2 + log ((1 + x)/(1 - x))`
  have hlog : Real.log θ
      = k * Real.log 2 + Real.log ((1 + seriesArg k θ) / (1 - seriesArg k θ)) := by
    have hdiv : (1 + seriesArg k θ) / (1 - seriesArg k θ) = θ / 2 ^ k := by
      rw [seriesArg]
      field_simp
      ring
    rw [hdiv, Real.log_div hθ.ne' hpow.ne', Real.log_zpow]
    ring
  have htwo : |k * Real.log 2 - k * ((logTwoLo + logTwoHi) / 2)|
      ≤ |(k : ℝ)| * ((logTwoHi - logTwoLo) / 2) := by
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg _) <;>
      linarith [log_two_mem.1, log_two_mem.2]
  -- Mathlib: the sum of `n` terms differs from `½ log ((1 + x)/(1 - x))` by at most
  -- `|x|^(2n+1)/(1 - x²)`. We use `|x|^(2n+1) ≤ x^(2n)`, which is free of absolute values.
  have hseries := (Real.sum_range_sub_log_div_le hx n).trans
    (div_le_div_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg _) hx.le (Nat.le_succ _)) hsq.le)
  rw [(even_two_mul n).pow_abs] at hseries
  rw [abs_le] at htwo hseries
  rw [hlog, logApprox, logErr]
  constructor <;> linarith [htwo.1, htwo.2, hseries.1, hseries.2]

private lemma log_three_mem : Real.log 3 ∈ Set.Icc logThreeLo logThreeHi :=
  ⟨le_trans (by numerics) (log_mem 2 7).1, (log_mem 2 7).2.trans (by numerics)⟩

/-! ## The exponent `q` of the query time (Corollary 31) -/

/-- `q(θ)` written out in terms of `log 2` and `log 3`. -/
private lemma qOf_eq_div (θ : ℝ) :
    qOf θ = (-θ * Real.log θ - (1 - θ) * Real.log (1 - θ) + θ * (2 * Real.log 3))
      / (2 * Real.log 2) := by
  unfold qOf entropy
  rw [Real.log_four, Real.log_nine]

/-- An upper bound on `q(θ)` at a rational `θ`. The hypothesis `h` is `H(θ) + θ ln 9 ≤ r ln 4` with
every logarithm replaced by the bound that makes the inequality harder. Here `2^k` is the power of
two nearest to `θ`; four terms of the series for `log θ` and for `log (1 - θ)` are enough for every
entry of Table 2. -/
theorem qOf_le (k : ℤ) {θ r : ℝ} (h0 : 0 < θ := by numerics) (h1 : θ < 1 := by numerics)
    (hr : 0 ≤ r := by numerics)
    (h : -θ * (logApprox k 4 θ - logErr k 4 θ)
        - (1 - θ) * (logApprox 0 4 (1 - θ) - logErr 0 4 (1 - θ)) + θ * (2 * logThreeHi)
      ≤ r * (2 * logTwoLo) := by numerics) : qOf θ ≤ r := by
  have hcompl := sub_pos.2 h1
  rw [qOf_eq_div, div_le_iff₀ (mul_pos two_pos (Real.log_pos one_lt_two))]
  have hlog := mul_le_mul_of_nonneg_left (log_mem k 4 h0).1 h0.le
  have hlogc := mul_le_mul_of_nonneg_left (log_mem 0 4 hcompl).1 hcompl.le
  have hthree := mul_le_mul_of_nonneg_left log_three_mem.2 h0.le
  have htwo := mul_le_mul_of_nonneg_left log_two_mem.1 hr
  linarith [h, hlog, hlogc, hthree, htwo]

/-- A lower bound on `q(θ)` at a rational `θ`, computed as in `qOf_le`. -/
theorem le_qOf (k : ℤ) {θ r : ℝ} (h0 : 0 < θ := by numerics) (h1 : θ < 1 := by numerics)
    (hr : 0 ≤ r := by numerics)
    (h : r * (2 * logTwoHi)
      ≤ -θ * (logApprox k 4 θ + logErr k 4 θ)
        - (1 - θ) * (logApprox 0 4 (1 - θ) + logErr 0 4 (1 - θ)) + θ * (2 * logThreeLo) := by
      numerics) : r ≤ qOf θ := by
  have hcompl := sub_pos.2 h1
  rw [qOf_eq_div, le_div_iff₀ (mul_pos two_pos (Real.log_pos one_lt_two))]
  have hlog := mul_le_mul_of_nonneg_left (log_mem k 4 h0).2 h0.le
  have hlogc := mul_le_mul_of_nonneg_left (log_mem 0 4 hcompl).2 hcompl.le
  have hthree := mul_le_mul_of_nonneg_left log_three_mem.1 h0.le
  have htwo := mul_le_mul_of_nonneg_left log_two_mem.2 hr
  linarith [h, hlog, hlogc, hthree, htwo]

/-! ## The exponent `γ` (Corollary 31) -/

/-! ## The bound `R_c(γ)` (equation (11)) -/

/-! ## Entries of Table 2

An entry needs two facts on its row, `hg` (an enclosure of `ln(1/ρ_c)/ln 4`) and `hR` (the `ε` of
the row is below `R_c(γ)` up to the largest `γ` of the row), and two rational numbers `θlo ≤ θhi`
that enclose its `θ`. -/

end ThreeSumApsp