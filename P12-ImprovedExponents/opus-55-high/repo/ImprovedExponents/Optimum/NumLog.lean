
import ThreeSumApsp.Sec4.Table2.LogBounds
import ImprovedExponents.Optimum.PerCCrossing
noncomputable section


/-!
# Certified rational bounds for the functions of the optimization

Every function of `Optimum/Defs.lean` is, at rational arguments, a rational combination of
logarithms of rational numbers. Upstream's `ThreeSumApsp.log_mem` encloses such a logarithm between
two rational numbers. This file turns a bound on `γX(c, θ)`, `γ_Q(θ)`, `c H(1/c)`, `baseFull c`,
`basePruned c`, `Γ(c)`, `R(γ)` or `F(γ)` into an inequality between rational numbers, which the
tactic `numlog` proves by evaluating both sides. Each lemma has this inequality as its last
hypothesis, with the default proof `by numlog`; so does every side condition on the arguments.

## The enclosures

`logLo k x ≤ log x ≤ logHi k x` (`log_mem4`), where `2^k` should be the power of two nearest to `x`.
The other enclosures are built from these two functions:

* `g2Lo k c δ ≤ g₂(c, δ) ≤ g2Hi k c δ` for `c > 1` and `0 ≤ δ < 1` (`g2_mem`); `2^k` near `c - 1`.
* `cEntLo k c ≤ c H(1/c) ≤ cEntHi k c` for `c > 1` (`cEntropy_mem`); `2^k` near `c`.

Both write the difference of two large terms as one logarithm near 1, for example
`ψ(c) - ψ(c - 1) = (c - 1) ln(c/(c - 1)) + ln c`, so that only one logarithm of a number far from 1
remains, with a small coefficient. The enclosure of `log y` has half-width
`2 x⁸/(1 - x²) + |k| · 2.5 · 10⁻¹⁰` with `x = (y - 2^k)/(y + 2^k)`, at most `1.6 · 10⁻⁶` when `2^k`
is the nearest power of two. Hence `baseFull c` and `basePruned c` are enclosed within `10⁻⁶`, and
`γX(c, θ)` and `γ_Q(θ)` within `4 · 10⁻⁷` for `θ ≤ 1/5` (the term `ln(1 - θ)` is expanded around 1,
so the enclosures widen for larger `θ`). One bound costs about 0.3 seconds.

## The interface

For rational `c`, `θ`, `r` (written as numerals, e.g. `108 / 5` or `0.1164`):

* `gammaX_le k : γX(c, θ) ≤ r` and `le_gammaX k : r ≤ γX(c, θ)`, with `2^k` near `c - 1`;
* `gammaQ_le k : γ_Q(θ) ≤ r` and `le_gammaQ k : r ≤ γ_Q(θ)`, with `2^k` near `θ`
  (for `1/2 - q(θ)` use upstream's `qOf_le k` and `le_qOf k`);
* `cEntropy_le k`, `le_cEntropy k`, `basePruned_le k`, `le_basePruned k`, `baseFull_le k`,
  `le_baseFull k`, with `2^k` near `c`;
* `le_Gam hX hQ : r ≤ Γ(c)` from `r ≤ γX(c, θ)` and `r ≤ γ_Q(θ)` at any `θ`, and
  `Gam_le hX hQ : Γ(c) ≤ r` from `γX(c, θ) ≤ r` and `γ_Q(θ) ≤ r` (take `θ` near the crossing);
* `lt_thinR`, `thinR_lt`, `lt_savingF`, `savingF_lt`: bounds on `R(γ)` and `F(γ)` from bounds
  `Alo ≤ A ≤ Ahi` and `γlo ≤ γ ≤ γhi`;
* `savingF_lt_of_mem_Icc`: a cell of a grid, `F(A(c), Γ(c)) < s` for all `c₁ ≤ c ≤ c₂`, from
  `Alo ≤ A(c₁)` and `Γ(c₂) ≤ γhi`, for a nondecreasing `A` (`baseFull` or `basePruned`);
* `logTwo_mem`, `logFour_mem`, `logThree_mem`, `logTen_mem`: the rational bounds on `ln 2`,
  `ln 4`, `ln 3`, `ln 10`.

## Worked examples

The examples assume `open ImprovedExponents ThreeSumApsp Set`.

The exponent `Γ(22) = 0.076207…`, with `θ` on the two sides of the crossing `0.1160367…`
(`16 = 2^4` is near `c - 1 = 21`, and `1/8 = 2^(-3)` is near `θ`):

```
example : (0.0762 : ℝ) ≤ Gam 22 := le_Gam (θ := 0.116036) (le_gammaX 4) (le_gammaQ (-3))
example : Gam 22 ≤ (0.0763 : ℝ) := Gam_le (θ := 0.116037) (gammaX_le 4) (gammaQ_le (-3))
```

The thinness bound with pruned encodings at `c = 22`, from these and from a bound on its constant:

```
example : (0.0549 : ℝ) < thinR (basePruned 22) (Gam 22) :=
  lt_thinR (basePruned_pos (by norm_num)) (basePruned_le 4 : basePruned 22 ≤ 25.105)
    (Gam_pos (by norm_num)).le (Gam_le (θ := 0.116037) (gammaX_le 4) (gammaQ_le (-3)) :
      Gam 22 ≤ 0.0763)
```

A cell of a grid: the saving with pruned encodings for all `22 ≤ c ≤ 22.1`.

```
example {c : ℝ} (hc : c ∈ Icc (22 : ℝ) 22.1) : savingF (basePruned c) (Gam c) < 0.00212 :=
  savingF_lt_of_mem_Icc basePruned_monotoneOn (le_basePruned 4 : (25.1 : ℝ) ≤ basePruned 22)
    (Gam_le (θ := 0.116) (gammaX_le 4) (gammaQ_le (-3)) : Gam 22.1 ≤ 0.0767) hc
```
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

/-! ### The enclosing functions -/

/-- The lower end of upstream's enclosure of `log x` with four terms of the series; `2^k` should be
near `x`. -/
def logLo (k : ℤ) (x : ℝ) : ℝ := logApprox k 4 x - logErr k 4 x

/-- The upper end of upstream's enclosure of `log x` with four terms of the series; `2^k` should be
near `x`. -/
def logHi (k : ℤ) (x : ℝ) : ℝ := logApprox k 4 x + logErr k 4 x

/-- A lower bound on `g₂(c, δ)`, written as
`-(c - 1) ln((c - 1 + δ)/(c - 1)) - δ ln(c - 1 + δ) - (1 - δ) ln(1 - δ) + 2δ ln 3`;
`2^k` should be near `c - 1`. -/
def g2Lo (k : ℤ) (c δ : ℝ) : ℝ :=
  -(c - 1) * logHi 0 ((c - 1 + δ) / (c - 1)) - δ * logHi k (c - 1 + δ)
    - (1 - δ) * logHi 0 (1 - δ) + δ * (2 * logThreeLo)

/-- An upper bound on `g₂(c, δ)`; `2^k` should be near `c - 1`. -/
def g2Hi (k : ℤ) (c δ : ℝ) : ℝ :=
  -(c - 1) * logLo 0 ((c - 1 + δ) / (c - 1)) - δ * logLo k (c - 1 + δ)
    - (1 - δ) * logLo 0 (1 - δ) + δ * (2 * logThreeHi)

/-- A lower bound on `c H(1/c) = (c - 1) ln(c/(c - 1)) + ln c`; `2^k` should be near `c`. -/
def cEntLo (k : ℤ) (c : ℝ) : ℝ := (c - 1) * logLo 0 (c / (c - 1)) + logLo k c

/-- An upper bound on `c H(1/c) = (c - 1) ln(c/(c - 1)) + ln c`; `2^k` should be near `c`. -/
def cEntHi (k : ℤ) (c : ℝ) : ℝ := (c - 1) * logHi 0 (c / (c - 1)) + logHi k c

/-- Proves an equation or inequality between explicit rational numbers by evaluating both sides,
after unfolding the enclosing functions of this file and upstream's approximations of
logarithms. -/
macro "numlog" : tactic =>
  `(tactic| norm_num [logLo, logHi, g2Lo, g2Hi, cEntLo, cEntHi, logApprox, logErr, seriesArg,
    logTwoLo, logTwoHi, logThreeLo, logThreeHi, logTenLo, logTenHi, Finset.sum_range_succ, rhoC])

variable (k : ℤ)

/-! ### Logarithms -/

/-- `logLo k x ≤ log x ≤ logHi k x` for `x > 0` (upstream's `log_mem` with four terms). -/
theorem log_mem4 {x : ℝ} (hx : 0 < x) : log x ∈ Icc (logLo k x) (logHi k x) :=
  log_mem k 4 hx

/-- `ln 4 = 2 ln 2` lies between `2 logTwoLo` and `2 logTwoHi`. -/
theorem logFour_mem : log 4 ∈ Icc (2 * logTwoLo) (2 * logTwoHi) := by
  have h := log_two_mem
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
  simp_all

variable {c : ℝ}

/-! ### The exponent `γX` -/

/-- `g2Lo k c δ ≤ g₂(c, δ) ≤ g2Hi k c δ` for `c > 1` and `0 ≤ δ < 1`. -/
theorem g2_mem {δ : ℝ} (hc : 1 < c) (h0 : 0 ≤ δ) (h1 : δ < 1) :
    g2 c δ ∈ Icc (g2Lo k c δ) (g2Hi k c δ) := by
  have hc1 := sub_pos.2 hc
  have hcδ : 0 < c - 1 + δ := by linarith
  have hδ1 := sub_pos.2 h1
  have heq : g2 c δ = -(c - 1) * log ((c - 1 + δ) / (c - 1)) - δ * log (c - 1 + δ)
      - (1 - δ) * log (1 - δ) + δ * 2 * log 3 := by
    rw [g2, log_div hcδ.ne' hc1.ne', show (9 : ℝ) = 3 ^ 2 by norm_num]
    simp [negMulLog]
    grind
  have hA := log_mem4 0 (div_pos hcδ hc1)
  have hB := log_mem4 k hcδ
  have hC := log_mem4 0 hδ1
  have h3 := log_three_mem
  rw [g2Lo, g2Hi]
  constructor
  · linarith [mul_le_mul_of_nonneg_left hA.2 hc1.le, mul_le_mul_of_nonneg_left hB.2 h0,
      mul_le_mul_of_nonneg_left hC.2 hδ1.le, mul_le_mul_of_nonneg_left h3.1 h0]
  · linarith [mul_le_mul_of_nonneg_left hA.1 hc1.le, mul_le_mul_of_nonneg_left hB.1 h0,
      mul_le_mul_of_nonneg_left hC.1 hδ1.le, mul_le_mul_of_nonneg_left h3.2 h0]

variable {r θ : ℝ}

/-- An upper bound `γX(c, θ) ≤ r` at rational arguments; `2^k` should be near `c - 1`. -/
theorem gammaX_le (hc : 1 < c := by numlog) (h0 : 0 ≤ θ := by numlog)
    (h1 : θ < 1 := by numlog) (hr : 0 ≤ r := by numlog)
    (h : -g2Lo k c θ ≤ r * (2 * logTwoLo) := by numlog) : gammaX c θ ≤ r := by
  rw [gammaX, div_le_iff₀ log_four_pos]
  linarith [(g2_mem k hc h0 h1).1, mul_le_mul_of_nonneg_left logFour_mem.1 hr]

/-- A lower bound `r ≤ γX(c, θ)` at rational arguments; `2^k` should be near `c - 1`. -/
theorem le_gammaX (hc : 1 < c := by numlog) (h0 : 0 ≤ θ := by numlog)
    (h1 : θ < 1 := by numlog) (hr : 0 ≤ r := by numlog)
    (h : r * (2 * logTwoHi) ≤ -g2Hi k c θ := by numlog) : r ≤ gammaX c θ := by
  rw [gammaX, le_div_iff₀ log_four_pos]
  linarith [(g2_mem k hc h0 h1).2, mul_le_mul_of_nonneg_left logFour_mem.2 hr]

/-! ### The exponent `γ_Q` -/

/-- An upper bound `γ_Q(θ) ≤ r` at a rational `θ`, by upstream's `le_qOf`; `2^k` should be near
`θ`. It needs `r ≤ 2/3`. -/
theorem gammaQ_le (h0 : 0 < θ := by numlog) (h1 : θ < 1 := by numlog)
    (hr : 0 ≤ (2 - 3 * r) / 4 := by numlog)
    (h : (2 - 3 * r) / 4 * (2 * logTwoHi)
      ≤ -θ * logHi k θ - (1 - θ) * logHi 0 (1 - θ) + θ * (2 * logThreeLo) := by numlog) :
    gammaQ θ ≤ r := by
  have hq := le_qOf k h0 h1 hr h
  unfold gammaQ
  linarith

/-- A lower bound `r ≤ γ_Q(θ)` at a rational `θ`, by upstream's `qOf_le`; `2^k` should be near
`θ`. It needs `r ≤ 2/3`. -/
theorem le_gammaQ (h0 : 0 < θ := by numlog) (h1 : θ < 1 := by numlog)
    (hr : 0 ≤ (2 - 3 * r) / 4 := by numlog)
    (h : -θ * logLo k θ - (1 - θ) * logLo 0 (1 - θ) + θ * (2 * logThreeHi)
      ≤ (2 - 3 * r) / 4 * (2 * logTwoLo) := by numlog) : r ≤ gammaQ θ := by
  have hq := qOf_le k h0 h1 hr h
  unfold gammaQ
  linarith

/-! ### The exponent `Γ` -/

/-- A lower bound on `Γ(c)` from lower bounds on `γX(c, θ)` and `γ_Q(θ)` at one `θ`. -/
theorem le_Gam (hX : r ≤ gammaX c θ) (hQ : r ≤ gammaQ θ) (hc : 10 < c := by numlog)
    (h0 : 0 < θ := by numlog) (h9 : θ < 9 / 10 := by numlog) : r ≤ Gam c :=
  by grind [le_min, Gam_ge_min]

/-- An upper bound on `Γ(c)` from upper bounds on `γX(c, θ)` and `γ_Q(θ)` at one `θ`. -/
theorem Gam_le (hX : gammaX c θ ≤ r) (hQ : gammaQ θ ≤ r) (hc : 10 < c := by numlog)
    (h0 : 0 < θ := by numlog) (h9 : θ < 9 / 10 := by numlog) : Gam c ≤ r :=
  by grind [Gam_le_max]

/-! ### The thinness constants -/

/-- `cEntLo k c ≤ c H(1/c) ≤ cEntHi k c` for `c > 1`. -/
theorem cEntropy_mem (hc : 1 < c) : cEntropy c ∈ Icc (cEntLo k c) (cEntHi k c) := by
  have hc1 := sub_pos.2 hc
  have hc0 : 0 < c := by linarith
  have heq : cEntropy c = (c - 1) * log (c / (c - 1)) + log c := by
    grind [cEntropy, log_div, negMulLog]
  have hA := log_mem4 0 (div_pos hc0 hc1)
  have hB := log_mem4 k hc0
  rw [cEntLo, cEntHi]
  exact ⟨by linarith [mul_le_mul_of_nonneg_left hA.1 hc1.le, hB.1],
    by linarith [mul_le_mul_of_nonneg_left hA.2 hc1.le, hB.2]⟩

/-- An upper bound `basePruned c ≤ r` at a rational `c`; `2^k` should be near `c`. -/
theorem basePruned_le (hc : 1 < c := by numlog)
    (h : 1 / 2 * cEntHi k c + (c - 1) * logThreeHi ≤ r := by numlog) : basePruned c ≤ r := by
  rw [basePruned_eq hc]
  linarith [(cEntropy_mem k hc).2,
    mul_le_mul_of_nonneg_left log_three_mem.2 (sub_pos.2 hc).le]

/-- A lower bound `r ≤ basePruned c` at a rational `c`; `2^k` should be near `c`. -/
theorem le_basePruned (hc : 1 < c := by numlog)
    (h : r ≤ 1 / 2 * cEntLo k c + (c - 1) * logThreeLo := by numlog) : r ≤ basePruned c := by
  rw [basePruned_eq hc]
  linarith [(cEntropy_mem k hc).1,
    mul_le_mul_of_nonneg_left log_three_mem.1 (sub_pos.2 hc).le]

/-! ### The thinness bound `R` and the saving `F` -/

/-- `F(γ) = γ ln 4/(2 (A + γ ln 4))`. -/
theorem savingF_eq_div (A γ : ℝ) : savingF A γ = γ * log 4 / (2 * (A + γ * log 4)) := by
  grind [savingF, thinR, log]

/-- A lower bound `s < F(γ)` from an upper bound `A ≤ Ahi` and a lower bound `γlo ≤ γ`. -/
theorem lt_savingF {A γ Ahi γlo s : ℝ} (hA : 0 < A) (hAhi : A ≤ Ahi) (hγ : γlo ≤ γ)
    (hγlo : 0 ≤ γlo := by numlog) (hs0 : 0 ≤ s := by numlog) (hs : s ≤ 1 / 2 := by numlog)
    (h : 2 * s * Ahi < γlo * (1 - 2 * s) * (2 * logTwoLo) := by numlog) : s < savingF A γ := by
  have h4 := logFour_mem
  have hγ0 := hγlo.trans hγ
  have hlo : 0 ≤ 2 * logTwoLo := by numlog
  have h1 : γlo * (1 - 2 * s) * (2 * logTwoLo) ≤ γ * (1 - 2 * s) * log 4 :=
    by grind [mul_le_mul, mul_le_mul_of_nonneg_right, mul_nonneg]
  have h2 : 2 * s * A ≤ 2 * s * Ahi := by grind [mul_le_mul_of_nonneg_left]
  rw [savingF_eq_div, lt_div_iff₀ (by positivity)]
  linarith
