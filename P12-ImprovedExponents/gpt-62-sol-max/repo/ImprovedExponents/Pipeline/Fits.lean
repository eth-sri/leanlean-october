module

public import ImprovedExponents.Pipeline.Ratios

public import ImprovedExponents.Pipeline.RegimeRS
public import ImprovedExponents.Optimum.PerCBasic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import all ThreeSumApsp.Sec4.Corollary31

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

open ThreeSumApsp Light.Sec4 Real Filter
open scoped Topology

/-- `binom(L, m) ≤ e^{m · (L/m) H(m/L)}`, with `c H(1/c)` written as `cEntropy c`. -/
theorem K_le_exp {L m : ℕ} (hm : 1 ≤ m) (hmL : m ≤ L) :
    (K L m : ℝ) ≤ exp ((m : ℝ) * cEntropy ((L : ℝ) / m)) := by
  have hm0 : (0 : ℝ) < m := by positivity
  have e : (L : ℝ) / m - 1 = ((L - m : ℕ) : ℝ) / m := by
    push_cast [Nat.cast_sub hmL]
    field_simp
  have he : (m : ℝ) * cEntropy (L / m) = chooseEntropy L m := by
    rw [cEntropy, e, mul_sub, mul_negMulLog_div hm0, mul_negMulLog_div hm0, chooseEntropy]
    simp only [Nat.cast_sub hmL, negMulLog]
    ring
  rw [he]
  exact (choose_entropyBounds hmL).1

/-- `√K N₀ ≤ e^{m A(L/m)}` with `A(c) = (c/2) H(1/c) + (c - 1) ln 3`. -/
theorem sqrtKN0_le_exp {L m : ℕ} (hm : 1 ≤ m) (hmL : m < L) :
    sqrtKN0 L m ≤ exp ((m : ℝ) * basePruned ((L : ℝ) / m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hLm : (1 : ℝ) < (L : ℝ) / m := by
    rw [one_lt_div hm0]
    exact_mod_cast hmL
  have hK := K_le_exp hm hmL.le
  have hsqrt : Real.sqrt (K L m : ℝ) ≤ exp ((m : ℝ) * cEntropy ((L : ℝ) / m) / 2) := by
    rw [show exp ((m : ℝ) * cEntropy ((L : ℝ) / m) / 2)
        = Real.sqrt (exp ((m : ℝ) * cEntropy ((L : ℝ) / m))) by
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
      lia]
    exact Real.sqrt_le_sqrt hK
  have hN0 : (N0 L m : ℝ) = exp (((L : ℝ) - m) * log 3) := by
    rw [N0, Nat.cast_pow, ← Nat.cast_sub hmL.le, exp_nat_mul, exp_log (by norm_num)]
    norm_num
  rw [sqrtKN0, basePruned_eq hLm, hN0]
  calc Real.sqrt (K L m : ℝ) * exp (((L : ℝ) - m) * log 3)
      ≤ exp ((m : ℝ) * cEntropy ((L : ℝ) / m) / 2) * exp (((L : ℝ) - m) * log 3) :=
        mul_le_mul_of_nonneg_right hsqrt (exp_pos _).le
    _ = exp ((m : ℝ) * (1 / 2 * cEntropy ((L : ℝ) / m) + ((L : ℝ) / m - 1) * log 3)) := by
        rw [← exp_add]
        congr 1
        field_simp

open private levelsOf_le from ThreeSumApsp.Sec4.Corollary31

private theorem levelRatio_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => (levelsOf c m : ℝ) / m) atTop (𝓝 c) := by
  have h := (tendsto_nat_ceil_div_atTop.comp (Tendsto.const_mul_atTop hc
    (tendsto_natCast_atTop_atTop (R := ℝ)))).const_mul c
  refine (by simpa only [mul_one] using h : Tendsto _ atTop (𝓝 c)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  change c * ((levelsOf c m : ℝ) / (c * m)) = _
  field_simp

/-- Strict slack in the exponential rate absorbs both the ceiling in the number of levels
and the factor `L` in the encoding work. -/
theorem eventually_tile_bound {c γ ε : ℝ} (hc : 10 < c) (hε : 0 < ε)
    (hA : basePruned c + γ * log 4 < log 4 / ε) :
    ∀ᶠ m : ℕ in atTop, ∀ D₀ N : ℕ, 4 ^ (m - 1) < D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m) ≤ (N : ℝ) := by
  let A := log 4 / ε
  let B := (basePruned c + A - γ * log 4) / 2
  let η := A - B - γ * log 4
  have hη : 0 < η := by dsimp [η, B, A]; linarith
  have hb : basePruned c < B := by dsimp [B, A]; linarith
  have hc0 : 0 < c := by linarith
  have hcont := basePruned_continuousOn.continuousAt (Ioi_mem_nhds hc)
  have hcoef := (hcont.tendsto.comp (levelRatio_tendsto hc0)).eventually (gt_mem_nhds hb)
  have hexp := (((isLittleO_pow_exp_pos_mul_atTop 1 hη).const_mul_left ((c + 1) * exp A)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound zero_lt_one
  filter_upwards [eventually_ge_atTop 1, hcoef, hexp] with m hm hB hE
  intro D₀ N hD hN
  have hmL := ten_mul_le_levelsOf hc m
  have hml : m < levelsOf c m := by omega
  have hL : (levelsOf c m : ℝ) ≤ exp (η * m - A) := by
    refine (levelsOf_le hc hm).trans ?_
    have he : (c + 1) * exp A * (m : ℝ) ≤ exp (η * m) := by
      simpa [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ c + 1), abs_exp] using hE
    rw [exp_sub, le_div_iff₀ (exp_pos A)]
    linarith
  have hroot := (sqrtKN0_le_exp hm hml).trans
    (exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt hB) (Nat.cast_nonneg m)))
  have hroot0 := (sqrtKN0_pos hml.le).le
  rw [cast_D_rpow]
  calc exp (γ * ((m : ℝ) * log 4)) * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m)
      ≤ exp (γ * ((m : ℝ) * log 4)) * (exp (η * m - A) * exp (m * B)) := by gcongr
    _ = exp (((m : ℝ) - 1) * A) := by rw [← exp_add, ← exp_add]; congr 1; dsimp [η]; ring
    _ ≤ N := by
      have h := Corollary31.hypothesis hm hε hD hN
      rw [rpow_def_of_pos (by norm_num), show log 4 * (((m : ℝ) - 1) / ε) = ((m : ℝ) - 1) * A by
        dsimp [A]; ring] at h
      exact h

theorem exists_fitsRS (G : RatParams) {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (h : basePruned G.realC < ((r : ℝ) / s) * log 4) :
    ∃ m₂ : ℕ, ∀ (m₀ : ℕ) (hm₀ : 1 ≤ m₀), m₂ ≤ m₀ →
      FitsRS (G.withThreshold m₀ hm₀) r s := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hcR := G.ten_lt_realC
  have heq : log 4 / ((s : ℝ) / r) = ((r : ℝ) / s) * log 4 := by field_simp
  obtain ⟨m₂, hbound⟩ := eventually_atTop.mp (eventually_tile_bound hcR (γ := 0)
    (div_pos hsR hrR) (by simpa only [zero_mul, add_zero, heq] using h))
  refine ⟨m₂, fun m₀ hm₀ h₂ N D₀ hN hm => ?_⟩
  let m := logFour D₀
  have hm1 : 1 ≤ m := hm₀.trans hm
  have hD := Nat.pow_pred_clog_lt_self (b := 4) (by norm_num) (two_le_of_clog hm1)
  have hn : (D₀ : ℝ) ≤ (N : ℝ) ^ ((s : ℝ) / r) := by
    rw [div_eq_mul_inv, Real.rpow_mul (by positivity), Real.rpow_natCast,
      le_rpow_inv_iff_of_pos (by positivity) (by positivity) hrR, Real.rpow_natCast]
    exact_mod_cast hN
  have hB := hbound m (h₂.trans hm) D₀ N hD hn
  have hL : 1 ≤ levelsOf G.realC m := by have := ten_mul_le_levelsOf hcR m; omega
  refine ⟨hm1, RatParams.ten_le_L _ _, RatParams.t_le _ _, ?_⟩
  change sqrtKN0 (G.L m) m ≤ (N : ℝ)
  rw [← show levelsOf G.realC m = G.L m from levelsOf_div G.a m G.hb]
  simp only [rpow_zero, one_mul] at hB
  exact (le_mul_of_one_le_left (sqrtKN0_pos (le_trans (by omega) (ten_mul_le_levelsOf hcR m))).le
    (Nat.one_le_cast.2 hL)).trans hB

end ImprovedExponents
