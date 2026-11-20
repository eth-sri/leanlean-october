module

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

section
variable {A γ : ℝ}
  (hA : 0 < A)
  (hγ : 0 ≤ γ)
include hA hγ

/-- The denominator `A + γ ln 4` of the thinness bound is positive for `A > 0` and `γ ≥ 0`. -/
theorem thinR_den_pos : 0 < A + γ * log 4 :=
  add_pos_of_pos_of_nonneg hA (mul_nonneg hγ log_four_pos.le)

/-- `R(γ) > 0` for `A > 0` and `γ ≥ 0`. -/
theorem thinR_pos : 0 < thinR A γ :=
  div_pos log_four_pos (thinR_den_pos hA hγ)

end

/-! ### The exponent `γ_Q` -/

/-! ### Continuity of `g₂` and `γX` in both variables -/

/-! ### The thinness constants `baseFull` and `basePruned` -/

/-- `c H(1/c)` for `c > 1`, written as `ψ(c) - ψ(c - 1)` with `ψ(x) = x ln x`, that is
`negMulLog (c - 1) - negMulLog c`. -/
noncomputable def cEntropy (c : ℝ) : ℝ := negMulLog (c - 1) - negMulLog c

/-- `c H(1/c) = ψ(c) - ψ(c - 1)` for `c > 1`. -/
theorem mul_entropy_one_div {c } (hc : 1 < c) : c * entropy (1 / c) = cEntropy c := by
  have hc0 : 0 < c := by linarith
  have h1 : 1 - 1 / c = (c - 1) / c := by grind
  rw [entropy, h1, log_div (sub_pos.2 hc).ne' hc0.ne', one_div, log_inv]
  simp [cEntropy, negMulLog]
  grind

/-- `cEntropy` is continuous. -/
theorem continuous_cEntropy : Continuous cEntropy := by
  unfold cEntropy
  fun_prop

section
variable {c : ℝ}
  (hc : 1 < c)
include hc

/-- `basePruned c = (1/2) c H(1/c) + (c - 1) ln 3`, with `c H(1/c)` as `cEntropy c`. -/
theorem basePruned_eq :
    basePruned c = 1 / 2 * cEntropy c + (c - 1) * log 3 := by
  rw [← mul_entropy_one_div hc, basePruned]
  ring

/-- `basePruned c > 0` for `c > 1`. -/
theorem basePruned_pos : 0 < basePruned c := by
  have hc0 : 0 < c := by linarith
  have hH :=
    entropy_nonneg (by positivity) ((div_le_one hc0).2 hc.le)
  have h3 : 0 < (c - 1) * log 3 := mul_pos (sub_pos.2 hc) (log_pos (by norm_num))
  have h2 := mul_nonneg (by positivity) hH
  unfold basePruned
  linarith

end

/-- `basePruned` is continuous on `(1, ∞)`. -/
theorem basePruned_continuousOn_Ioi_one : ContinuousOn basePruned (Ioi 1) := by
  have h : Continuous fun c : ℝ => 1 / 2 * cEntropy c + (c - 1) * log 3 := by
    have := continuous_cEntropy
    fun_prop
  exact h.continuousOn.congr fun x hx => basePruned_eq hx

/-- `basePruned` is continuous on `(10, ∞)`. -/
theorem basePruned_continuousOn : ContinuousOn basePruned (Ioi 10) :=
  basePruned_continuousOn_Ioi_one.mono (Ioi_subset_Ioi (by norm_num))

end ImprovedExponents
