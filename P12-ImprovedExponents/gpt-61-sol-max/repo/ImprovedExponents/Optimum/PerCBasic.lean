module

public import Mathlib.Tactic
public import ImprovedExponents.Optimum.Defs

@[expose] public section

/-!
# The saving for a fixed `c`: elementary facts

Small lemmas about the functions of `Optimum/Defs.lean`, for a fixed thinness constant `A > 0`.

* `thinR A γ = ln 4/(A + γ ln 4)` is positive and strictly decreasing in `γ ≥ 0`
  (`thinR_pos`, `thinR_strictAntiOn`), and decreasing in `A` (`thinR_antitone_left`).
* `savingF A γ = (1 - A/(A + γ ln 4))/2` increases strictly in `γ ≥ 0` (`savingF_strictMonoOn`)
  and decreases in `A` (`savingF_antitone_left`).
* `γ_Q` is continuous and strictly decreasing on `[0, 9/10]`, from `γ_Q(0) = 2/3` to
  `γ_Q(9/10) < 0` (`continuous_gammaQ`, `gammaQ_strictAntiOn`, `gammaQ_zero`,
  `gammaQ_nine_tenths_neg`).
* `g₂` and `γX` are continuous as functions of two variables (`continuous_g2`,
  `continuous_gammaX`).
* The two thinness constants `baseFull c` and `basePruned c` are positive, continuous and
  nondecreasing in `c` (`baseFull_pos`, `basePruned_pos`, `baseFull_continuousOn`,
  `basePruned_continuousOn`, `baseFull_monotoneOn`, `basePruned_monotoneOn`). The proofs write
  `c H(1/c) = ψ(c) - ψ(c - 1)` with `ψ(x) = x ln x` (`mul_entropy_one_div`), whose derivative is
  `ln c - ln(c - 1)`.
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

/-! ### The thinness bound `R` and the saving `F` -/

/-- The denominator `A + γ ln 4` of the thinness bound is positive for `A > 0` and `γ ≥ 0`. -/
def thinR_den_pos {A γ : ℝ} (hA : 0 < A) (hγ : 0 ≤ γ) :=
  add_pos_of_pos_of_nonneg hA (mul_nonneg hγ log_four_pos.le)

/-- `R(γ) > 0` for `A > 0` and `γ ≥ 0`. -/
def thinR_pos {A γ : ℝ} (hA : 0 < A) (hγ : 0 ≤ γ) :=
  div_pos log_four_pos (thinR_den_pos hA hγ)

/-! ### The exponent `γ_Q` -/

/-! ### Continuity of `g₂` and `γX` in both variables -/

/-! ### The thinness constants `baseFull` and `basePruned` -/

/-- `c H(1/c)` for `c > 1`, written as `ψ(c) - ψ(c - 1)` with `ψ(x) = x ln x`, that is
`negMulLog (c - 1) - negMulLog c`. -/
noncomputable def cEntropy c := negMulLog (c - 1) - negMulLog c

/-- `c H(1/c) = ψ(c) - ψ(c - 1)` for `c > 1`. -/
theorem mul_entropy_one_div {c} (hc : 1 < c) : c * entropy (1 / c) = cEntropy c := by


  rw [entropy, (by field_simp : 1 - 1 / c = (c - 1) / c), log_div (sub_pos.2 hc).ne' (by linarith : 0 < c).ne', one_div, log_inv]
  simp only [cEntropy, negMulLog]
  field_simp
  ring

/-- `cEntropy` is continuous. -/
theorem continuous_cEntropy : Continuous cEntropy := by
  unfold cEntropy
  fun_prop

/-- `basePruned c = (1/2) c H(1/c) + (c - 1) ln 3`, with `c H(1/c)` as `cEntropy c`. -/
theorem basePruned_eq {c} (hc : 1 < c) :
    basePruned c = 1 / 2 * cEntropy c + (c - 1) * log 3 := by
  grind [mul_entropy_one_div, basePruned]

/-- `basePruned c > 0` for `c > 1`. -/
theorem basePruned_pos {c} (hc : 1 < c) : 0 < basePruned c := by

  have hH :=
    entropy_nonneg (by positivity) ((div_le_one (by linarith)).2 hc.le)
  have  : 0 < (c - 1) * log 3 := mul_pos (sub_pos.2 hc) (log_pos (by norm_num))
  have  := mul_nonneg (by positivity) hH
  unfold basePruned
  linarith

/-- `basePruned` is continuous on `(1, ∞)`. -/
theorem basePruned_continuousOn_Ioi_one : ContinuousOn basePruned (Ioi 1) := by

  exact (by
    have := continuous_cEntropy
    fun_prop
   : Continuous fun c  => 1 / 2 * cEntropy c + (c - 1) * log 3).continuousOn.congr fun x hx => basePruned_eq hx

/-- `basePruned` is continuous on `(10, ∞)`. -/
theorem basePruned_continuousOn : ContinuousOn basePruned (Ioi 10) :=
  basePruned_continuousOn_Ioi_one.mono (Ioi_subset_Ioi (by norm_num))

end ImprovedExponents
