
import ImprovedExponents.Pipeline.RegimeRS
import ImprovedExponents.Optimum.PerCBasic


/-!
# The tile fits in the whole regime of the program's test

The solver of `ImprovedExponents.Pipeline.ThinClaim` runs the recursion whenever the instance is in
the regime of its test, so the hypotheses of Theorem 30 must hold there (`FitsRS` for the test
`D^r ≤ N^s` of `ImprovedExponents.Pipeline.RegimeRS`, `Fits18` for the program's test `D^18 ≤ N`).
The one that matters is `√K N₀ ≤ N`: the `N₀ × N₀` tiles, `√K` to a band, must fit into the matrix.

With `L = ⌈cm⌉`, `√K N₀ ≤ e^{m A(L/m)}` for `A(c) = (c/2) H(1/c) + (c - 1) ln 3` (`basePruned`), and
`N^s ≥ D^r > 4^{r(m-1)}`. So the tile fits for all large `m` exactly when `A(c) < (r/s) ln 4`
(`exists_fitsRS`); for the program's test this is `A(c) < 18 ln 4` (`exists_fits18`), that is
`c < 21.85…`.
-/

namespace ImprovedExponents

open ThreeSumApsp Light.Sec4 Real

variable {m L : ℕ}

/-- `binom(L, m) ≤ e^{m · (L/m) H(m/L)}`, with `c H(1/c)` written as `cEntropy c`. -/
theorem K_le_exp (hm : 1 ≤ m) (hmL : m ≤ L) :
    (K L m : ℝ) ≤ exp ((m : ℝ) * cEntropy ((L : ℝ) / m)) := by
  have hm0 : (0 : ℝ) < m := by positivity
  -- the exponent, in terms of `ψ` at natural numbers
  have hexp : m * cEntropy (L / m)
      = negMulLog (L - m : ℕ) - negMulLog L + negMulLog m := by
    have e1 : L / m - 1 = ((L - m : ℕ) : ℝ) / m := by
      grind [Nat.cast_sub]
    have hlog : negMulLog m = -m * log m := by grind [negMulLog]
    grind [cEntropy, mul_sub, mul_negMulLog_div]
  have hval : exp (m * cEntropy (L / m))
      = L ^ L / ((L - m : ℕ) ^ (L - m) * m ^ m) := by
    rw [← (exp_neg_negMulLog_natCast (L - m)), ← exp_neg_negMulLog_natCast L, ← exp_neg_negMulLog_natCast m, ← exp_add, ← exp_sub]
    grind
  have hpos : 0 < (L - m : ℕ) ^ (L - m) * (m : ℝ) ^ m := by
    have h : 0 < (L - m) ^ (L - m) * m ^ m := Nat.mul_pos Nat.pow_self_pos (by simp_all)
    exact_mod_cast h
  rw [hval, le_div_iff₀ hpos]
  have hnat : L.choose m * m ^ m * (L - m) ^ (L - m) ≤ L ^ L := by
    have h := m.choose_mul_pow_mul_pow_le (L - m) L m
    simp_all
  have hcast : L.choose m * m ^ m * (L - m : ℕ) ^ (L - m) ≤ (L : ℝ) ^ L := by
    exact_mod_cast hnat
  grind [K]

/-- `√K N₀ ≤ e^{m A(L/m)}` with `A(c) = (c/2) H(1/c) + (c - 1) ln 3`. -/
theorem sqrtKN0_le_exp (hm : 1 ≤ m) (hmL : m < L) :
    sqrtKN0 L m ≤ exp ((m : ℝ) * basePruned ((L : ℝ) / m)) := by
  have hm0 : 0 < m := by positivity
  have hLm : 1 < (L : ℝ) / m := by
    simp_all [one_lt_div]
  have hsqrt : Real.sqrt (K L m) ≤ exp (m * cEntropy (L / m) / 2) := by
    rw [show exp _
        = Real.sqrt (exp (m * cEntropy (L / m))) by
      grind [Real.sqrt_eq_rpow, Real.exp_mul]]
    grind [Real.sqrt_le_sqrt, K_le_exp]
  have hN0 : N0 L m = exp ((L - m) * log 3) := by
    rw [N0, ← Nat.cast_sub hmL.le, exp_nat_mul, exp_log (by norm_num)]
    norm_num
  rw [sqrtKN0, basePruned_eq hLm, hN0]
  calc Real.sqrt _ * exp _
      ≤ exp _ * exp _ :=
        mul_le_mul_of_nonneg_right hsqrt (exp_pos _).le
    _ = exp _ := by
        rw [← exp_add]
        grind

/-- **The tile fits in the regime `D^r ≤ N^s`** for all large thresholds, if
`(c/2) H(1/c) + (c - 1) ln 3 < (r/s) ln 4` at the ratio `c = a/b`. -/
theorem exists_fitsRS {a b p q : ℕ} (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a) (hp : 1 ≤ p)
    (hθ : 10 * p < 9 * q) {r s : ℕ} (hs : 1 ≤ s)
    (h : basePruned ((a : ℝ) / b) < ((r : ℝ) / s) * log 4) :
    ∃ m₂ : ℕ, ∀ (m₀ : ℕ) (hm₀ : 1 ≤ m₀), m₂ ≤ m₀ →
      FitsRS ⟨a, b, p, q, m₀, hb, hq, hc, hp, hθ, hm₀⟩ r s := by
  have hbR : (0 : ℝ) < b := by positivity
  have hsR : (0 : ℝ) < s := by positivity
  have hcR : 10 < (a : ℝ) / b := by
    rw [lt_div_iff₀ hbR]
    exact_mod_cast hc
  set c : ℝ := a / b with hcdef
  set B : ℝ := (basePruned c + (r / s) * log 4) / 2 with hBdef
  have hB1 : basePruned c < B := by linarith
  have hB2 : B < r / s * log 4 := by linarith
  -- `s B < r ln 4`
  have hsB : s * B < r * log 4 := by
    have := (lt_div_iff₀ hsR).1 (by rwa [div_mul_eq_mul_div] at hB2)
    linarith
  -- near `c` the constant stays below `B`
  have hcont :=
    basePruned_continuousOn.continuousAt (Ioi_mem_nhds hcR)
  obtain ⟨δ₀, hδ₀, hnear⟩ := Metric.eventually_nhds_iff.1
    (hcont.eventually (gt_mem_nhds hB1))
  have hgap : 0 < r * log 4 - s * B := by linarith
  refine ⟨max ⌈1 / δ₀⌉₊ ⌈r * log 4 / (r * log 4 - s * B)⌉₊, fun m₀ hm₀ hm₂ N D₀ hN hm => ?_⟩
  set m := logFour D₀ with hmdef
  have hm1 : 1 ≤ m := by grind
  have hm0 : (0 : ℝ) < m := by positivity
  have hmδ : 1 / δ₀ ≤ m :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by grind))
  have hmB : r * log 4 / (r * log 4 - s * B) ≤ m :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by grind))
  -- the levels
  have hLdef : (parOf ⟨a, b, p, q, m₀, hb, hq, hc, hp, hθ, hm₀⟩ N D₀).L = levelsOf c m := by
    rw [levelsOf_div a _ hb]
    rfl
  have hLge : c * m ≤ levelsOf c m := Nat.le_ceil _
  have hLlt : levelsOf c m < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmL : m < levelsOf c m := by
    have h : m < (levelsOf c m : ℝ) := by nlinarith
    simp_all
  have hratio1 : c ≤ levelsOf c m / m := by simp_all [le_div_iff₀]
  have hratio2 : levelsOf c m / m < c + δ₀ := by
    rw [div_lt_iff₀ hm0]
    have : 1 ≤ δ₀ * m := by
      have := (div_le_iff₀ hδ₀).1 hmδ
      linarith
    nlinarith
  have hbase : basePruned ((levelsOf c m) / m) < B := by
    grind [Real.dist_eq]
  -- `s m B ≤ r (m - 1) ln 4`
  have hexp : s * (m * B) ≤ (r * (m - 1) : ℕ) * log 4 := by
    have h1 : r * log 4 ≤ m * (r * log 4 - s * B) := by
      simp_all [div_le_iff₀]
    push_cast [Nat.cast_sub hm1]
    linarith
  have hfour : exp ((r * (m - 1) : ℕ) * log 4) = 4 ^ (r * (m - 1)) := by
    rw [exp_nat_mul, exp_log (by norm_num)]
  -- `4^{r(m-1)} ≤ D₀^r ≤ N^s`
  have hD2 := two_le_of_clog hm1
  have hpow : 4 ^ (m - 1) < D₀ := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hNge : 4 ^ (r * (m - 1)) ≤ (N : ℝ) ^ s := by
    have h := (Nat.pow_le_pow_left hpow.le r).trans hN
    rw [← pow_mul, mul_comm] at h
    exact_mod_cast h
  -- `e^{m B} ≤ N`, as `e^{s m B} ≤ N^s`
  have hmain : exp (m * B) ≤ N := by
    apply le_of_pow_le_pow_left₀ (by omega : s ≠ 0) (by positivity)
    rw [← exp_nat_mul]
    calc exp _ ≤ exp _ := exp_le_exp.2 hexp
      _ = 4 ^ (r * (m - 1)) := hfour
      _ ≤ N ^ s := hNge
  refine ⟨hm1, RatParams.ten_le_L _ _, RatParams.t_le _ _, ?_⟩
  rw [hLdef]
  calc sqrtKN0 _ m
      ≤ exp _ := sqrtKN0_le_exp hm1 hmL
    _ ≤ exp _ := exp_le_exp.2 (mul_le_mul_of_nonneg_left hbase.le hm0.le)
    _ ≤ N := hmain
