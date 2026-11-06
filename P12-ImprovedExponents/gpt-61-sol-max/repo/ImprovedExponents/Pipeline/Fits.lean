module

public import Mathlib.Tactic
public import ImprovedExponents.Pipeline.RegimeRS
public import ImprovedExponents.Optimum.PerCBasic

@[expose] public section

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

/-- `binom(L, m) ≤ e^{m · (L/m) H(m/L)}`, with `c H(1/c)` written as `cEntropy c`. -/
theorem K_le_exp {L m} (hm : 1 ≤ m) (hmL : m ≤ L) :
    (K L m : ℝ) ≤ exp (m * cEntropy (L / m)) := by
  have hm0 : (0 : ℝ) < m := mod_cast hm
  -- the exponent, in terms of `ψ` at natural numbers
  have hexp : (m : ℝ) * cEntropy (L / m)
      = negMulLog (L - m : ℕ) - negMulLog L + negMulLog m := by



    rw [cEntropy, (by
      push_cast [Nat.cast_sub hmL]
      field_simp
     : (L : ℝ) / m - 1 = ((L - m : ℕ) : ℝ) / m), mul_sub, mul_negMulLog_div hm0, mul_negMulLog_div hm0, (by rw [negMulLog]; ring : negMulLog m = -((m : ℝ) * log m))]
    linear_combination log m * (by
      simp_all
     : ((L - m : ℕ) : ℝ) - (L : ℝ) = -(m : ℝ))



  have hval : exp (m * cEntropy (L / m))
      = (L : ℝ) ^ L / (((L - m : ℕ) : ℝ) ^ (L - m) * (m : ℝ) ^ m) := by
    rw [hexp, ← exp_neg_negMulLog_natCast (L - m), ← exp_neg_negMulLog_natCast L, ← exp_neg_negMulLog_natCast m, ← exp_add, ← exp_sub]
    congr 1
    ring

  rw [hval, le_div_iff₀ (by
    have h : 0 < (L - m) ^ (L - m) * m ^ m := Nat.mul_pos Nat.pow_self_pos (Nat.pow_pos (by omega))
    exact_mod_cast h
  )]
  have hnat := by
    have h := Nat.choose_mul_pow_mul_pow_le m (L - m) L m
    rwa [Nat.add_sub_cancel' hmL] at h

  calc (K L m : ℝ) * (((L - m : ℕ) : ℝ) ^ (L - m) * (m : ℝ) ^ m)
      = (L.choose m : ℝ) * (m : ℝ) ^ m * ((L - m : ℕ) : ℝ) ^ (L - m) := by
        rw [K]
        ring
    _ ≤ (L : ℝ) ^ L := (mod_cast hnat)

/-- `√K N₀ ≤ e^{m A(L/m)}` with `A(c) = (c/2) H(1/c) + (c - 1) ln 3`. -/
theorem sqrtKN0_le_exp {L m} (hm : 1 ≤ m) (hmL : m < L) :
    sqrtKN0 L m ≤ exp (m * basePruned (L / m)) := by



  rw [sqrtKN0, basePruned_eq (by
    rw [one_lt_div (mod_cast hm)]
    exact_mod_cast hmL
  ), (by
    rw [N0, Nat.cast_pow, ← Nat.cast_sub hmL.le, exp_nat_mul, exp_log (by norm_num)]
    norm_num
   : (N0 L m : ℝ) = exp ((L - m) * log 3))]
  calc Real.sqrt (K L m) * exp ((L - m) * log 3)
      ≤ exp (m * cEntropy (L / m) / 2) * exp ((L - m) * log 3) :=
        mul_le_mul_of_nonneg_right (by
          rw [show exp (m * cEntropy (L / m) / 2)
              = Real.sqrt (exp (m * cEntropy (L / m))) by
            grind [Real.sqrt_eq_rpow, Real.exp_mul]]
          exact Real.sqrt_le_sqrt (K_le_exp hm hmL.le)
        ) (exp_pos _).le
    _ = exp (m * (1 / 2 * cEntropy (L / m) + (L / m - 1) * log 3)) := by
        rw [← exp_add]
        congr 1
        field_simp

/-- **The tile fits in the regime `D^r ≤ N^s`** for all large thresholds, if
`(c/2) H(1/c) + (c - 1) ln 3 < (r/s) ln 4` at the ratio `c = a/b`. -/
theorem exists_fitsRS {a b p q : ℕ} (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a) (hp : 1 ≤ p)
    (hθ : 10 * p < 9 * q) {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (h : basePruned (a / b) < (r : ℝ) / s * log 4) :
    ∃ m₂ : ℕ, ∀ m₀ (hm₀ : 1 ≤ m₀), m₂ ≤ m₀ →
      FitsRS ⟨a, b, p, q, m₀, hb, hq, hc, hθ⟩ r s := by

  have  : (0 : ℝ) < r := mod_cast hr

  have  := log_four_pos
  have hcR : (10 : ℝ) < (a : ℝ) / b := by
    rw [lt_div_iff₀ (mod_cast hb)]
    exact_mod_cast hc
  set c : ℝ := (a : ℝ) / b with hcdef
  set B : ℝ := (basePruned c + (r : ℝ) / s * log 4) / 2 with hBdef

  have hB2 : B < (r : ℝ) / s * log 4 := by rw [hBdef]; linarith
  -- `s B < r ln 4`
  have  : (s : ℝ) * B < r * log 4 := by
    have := (lt_div_iff₀ (mod_cast hs : (0 : ℝ) < s)).1 (by rwa [div_mul_eq_mul_div] at hB2)
    linarith
  -- near `c` the constant stays below `B`
  have hcont : ContinuousAt basePruned c :=
    basePruned_continuousOn.continuousAt (Ioi_mem_nhds hcR)
  obtain ⟨δ₀, hδ₀, hnear⟩ := Metric.eventually_nhds_iff.1
    (hcont.eventually (gt_mem_nhds (by rw [hBdef]; linarith : basePruned c < B)))

  refine ⟨max ⌈1 / δ₀⌉₊ ⌈r * log 4 / (r * log 4 - s * B)⌉₊, fun m₀ hm₀ hm₂ N D₀ hN hm => ?_⟩
  change m₀ ≤ logFour D₀ at hm
  set m := logFour D₀ with hmdef
  have hm1 : 1 ≤ m := le_trans hm₀ hm
  have hm0 : (0 : ℝ) < m := mod_cast hm1
  have hmδ : 1 / δ₀ ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by gcongr <;> first | assumption | positivity | omega)
  have hmB : r * log 4 / (r * log 4 - s * B) ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by gcongr <;> first | assumption | positivity | omega)
  -- the levels

  have  : c * m ≤ (levelsOf c m : ℝ) := Nat.le_ceil _
  have  : (levelsOf c m : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)

  have  : c ≤ (levelsOf c m : ℝ) / m := by rwa [le_div_iff₀ hm0]
  have  : (levelsOf c m : ℝ) / m < c + δ₀ := by
    rw [div_lt_iff₀ hm0]
    have : 1 ≤ δ₀ * m := by
      have := (div_le_iff₀ hδ₀).1 hmδ
      linarith
    nlinarith
  have hbase : basePruned (levelsOf c m / m) < B := by
    grind [Real.dist_eq]
  -- `s m B ≤ r (m - 1) ln 4`

  have hfour : exp ((r * (m - 1) : ℕ) * log 4) = (4 : ℝ) ^ (r * (m - 1)) := by
    rw [exp_nat_mul, exp_log (by norm_num)]
  -- `4^{r(m-1)} ≤ D₀^r ≤ N^s`
  have  := two_le_of_clog hm1

  have hNge : (4 : ℝ) ^ (r * (m - 1)) ≤ (N : ℝ) ^ s := by
    have h := (Nat.pow_le_pow_left (Nat.pow_pred_clog_lt_self (by norm_num) (by omega) : 4 ^ (m - 1) < D₀).le r).trans hN
    rw [← pow_mul, mul_comm] at h
    exact_mod_cast h
  -- `e^{m B} ≤ N`, as `e^{s m B} ≤ N^s`

  refine ⟨hm1, RatParams.ten_le_L _ _, RatParams.t_le _ _, ?_⟩
  change sqrtKN0 (parOf ⟨a, b, p, q, m₀, hb, hq, hc, hθ⟩ N D₀).L m ≤ (N : ℝ)
  rw [(by
    rw [levelsOf_div a _ hb]
    rfl
   : (parOf ⟨a, b, p, q, m₀, hb, hq, hc, hθ⟩ N D₀).L = levelsOf c m)]
  calc sqrtKN0 (levelsOf c m) m
      ≤ exp (m * basePruned (levelsOf c m / m)) := sqrtKN0_le_exp hm1 (by
        have h : (m : ℝ) < (levelsOf c m : ℝ) := by nlinarith
        exact_mod_cast h
      )
    _ ≤ exp (m * B) := exp_le_exp.2 (mul_le_mul_of_nonneg_left hbase.le hm0.le)
    _ ≤ (N : ℝ) := (by
      refine le_of_pow_le_pow_left₀ (by omega : s ≠ 0) (by positivity) ?_
      rw [← exp_nat_mul]
      calc exp (s * (m * B)) ≤ exp ((r * (m - 1) : ℕ) * log 4) := exp_le_exp.2 (by
        have h1 : r * log 4 ≤ (m : ℝ) * (r * log 4 - s * B) := by
          have := (div_le_iff₀ (by linarith)).1 hmB
          linarith
        push_cast [Nat.cast_sub hm1]
        linarith
      )
        _ = (4 : ℝ) ^ (r * (m - 1)) := hfour
        _ ≤ (N : ℝ) ^ s := hNge
    )

end ImprovedExponents
