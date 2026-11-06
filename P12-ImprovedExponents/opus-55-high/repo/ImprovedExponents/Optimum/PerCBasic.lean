
import ImprovedExponents.Optimum.Defs


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

variable {A γ : ℝ}

/-! ### The thinness bound `R` and the saving `F` -/

/-- The denominator `A + γ ln 4` of the thinness bound is positive for `A > 0` and `γ ≥ 0`. -/
theorem thinR_den_pos (hA : 0 < A) (hγ : 0 ≤ γ) : 0 < A + γ * log 4 :=
  by positivity

/-- `R(γ) > 0` for `A > 0` and `γ ≥ 0`. -/
theorem thinR_pos (hA : 0 < A) (hγ : 0 ≤ γ) : 0 < thinR A γ :=
  div_pos log_four_pos (by positivity)

/-- `R` decreases strictly in `γ ≥ 0`, for `A > 0`. -/
theorem thinR_strictAntiOn (hA : 0 < A) : StrictAntiOn (thinR A) (Ici 0) := by
  intro x hx y _ hxy
  apply div_lt_div_of_pos_left log_four_pos (thinR_den_pos hA hx)
  linarith [mul_lt_mul_of_pos_right hxy log_four_pos]


/-! ### The exponent `γ_Q` -/

/-- `γ_Q(0) = 2/3`. -/
@[simp] theorem gammaQ_zero : gammaQ 0 = 2 / 3 := by simp [gammaQ, qOf_zero]

/-- `γ_Q` is continuous. -/
theorem continuous_gammaQ : Continuous gammaQ :=
  (continuous_const.sub (continuous_const.mul continuous_qOf)).div_const _

/-- `q` increases strictly on `[0, 9/10]` (upstream's `qOf_strictMonoOn`, with `9/10` for
`0.9`). -/
theorem qOf_strictMonoOn' : StrictMonoOn qOf (Icc 0 (9 / 10)) := by
  have h := qOf_strictMonoOn
  rwa [show (0.9 : ℝ) = 9 / 10 by norm_num] at h

/-- `γ_Q` decreases strictly on `[0, 9/10]`. -/
theorem gammaQ_strictAntiOn : StrictAntiOn gammaQ (Icc 0 (9 / 10)) := by
  intro x hx y hy hxy
  have h := qOf_strictMonoOn' hx hy hxy
  unfold gammaQ
  linarith

/-- `q(9/10) = log_4 10 > 1`. -/
theorem one_lt_qOf_nine_tenths : 1 < qOf (9 / 10) := by
  rw [show (9 / 10 : ℝ) = 0.9 by norm_num, qOf_nine_tenths,
    lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
  norm_num

/-- `γ_Q(9/10) = (2 - 4 log_4 10)/3 < 0`. -/
theorem gammaQ_nine_tenths_neg : gammaQ (9 / 10) < 0 := by
  grind [one_lt_qOf_nine_tenths, gammaQ]

/-- `γ_Q(θ) = γ` exactly when `q(θ) = 1/2 - 3γ/4`. -/
theorem gammaQ_eq_iff {θ : ℝ} : gammaQ θ = γ ↔ qOf θ = 1 / 2 - 3 * γ / 4 := by
  unfold gammaQ
  grind

/-! ### Continuity of `g₂` and `γX` in both variables -/

/-- `g₂` is continuous as a function of two variables. -/
theorem continuous_g2 : Continuous fun p : ℝ × ℝ => g2 p.1 p.2 := by
  unfold g2
  fun_prop

/-- `γX` is continuous as a function of two variables. -/
theorem continuous_gammaX : Continuous fun p : ℝ × ℝ => gammaX p.1 p.2 :=
  continuous_g2.neg.div_const _

/-- `γX(c, ·)` is continuous. -/
theorem continuous_gammaX_right (c : ℝ) : Continuous (gammaX c) :=
  (continuous_g2_right c).neg.div_const _

/-! ### The thinness constants `baseFull` and `basePruned` -/

/-- `c H(1/c)` for `c > 1`, written as `ψ(c) - ψ(c - 1)` with `ψ(x) = x ln x`, that is
`negMulLog (c - 1) - negMulLog c`. -/
noncomputable def cEntropy (c : ℝ) : ℝ := negMulLog (c - 1) - negMulLog c

variable {c : ℝ}

/-- `c H(1/c) = ψ(c) - ψ(c - 1)` for `c > 1`. -/
theorem mul_entropy_one_div (hc : 1 < c) : c * entropy (1 / c) = cEntropy c := by
  have hc0 : 0 < c := by linarith
  have h1 : 1 - 1 / c = (c - 1) / c := by field_simp
  rw [entropy, h1, log_div (sub_pos.2 hc).ne' hc0.ne', one_div]
  simp [cEntropy, negMulLog]
  grind

/-- `cEntropy` is continuous. -/
theorem continuous_cEntropy : Continuous cEntropy := by
  unfold cEntropy
  fun_prop

/-- `d/dc [c H(1/c)] = ln c - ln(c - 1)`. -/
theorem hasDerivAt_cEntropy (hc : 1 < c := by linarith) :
    HasDerivAt cEntropy (log c - log (c - 1)) c := by
  have h1 :=
    (hasDerivAt_negMulLog (sub_pos.2 hc).ne').comp c ((hasDerivAt_id c).sub_const 1)
  have h : HasDerivAt cEntropy _ c := h1.sub (hasDerivAt_negMulLog (zero_lt_one.trans hc).ne')
  grind

/-- `basePruned c = (1/2) c H(1/c) + (c - 1) ln 3`, with `c H(1/c)` as `cEntropy c`. -/
theorem basePruned_eq (hc : 1 < c := by norm_num) :
    basePruned c = 1 / 2 * cEntropy c + (c - 1) * log 3 := by
  grind [mul_entropy_one_div, basePruned]

/-- `basePruned c > 0` for `c > 1`. -/
theorem basePruned_pos (hc : 1 < c := by linarith) : 0 < basePruned c := by
  have hc0 : 0 < c := by linarith
  have hH :=
    entropy_nonneg (by positivity) ((div_le_one hc0).2 hc.le)
  have h3 : 0 < (c - 1) * log 3 := by positivity
  have h2 : 0 ≤ c / 2 * entropy (1 / c) := by simp_all
  unfold basePruned
  linarith

/-- `basePruned` is continuous on `(1, ∞)`. -/
theorem basePruned_continuousOn_Ioi_one : ContinuousOn basePruned (Ioi 1) := by
  have h : Continuous fun c => 1 / 2 * cEntropy c + (c - 1) * log 3 := by
    have := continuous_cEntropy
    fun_prop
  exact h.continuousOn.congr fun x hx => basePruned_eq hx

/-- `basePruned` is continuous on `(10, ∞)`. -/
theorem basePruned_continuousOn : ContinuousOn basePruned (Ioi 10) :=
  basePruned_continuousOn_Ioi_one.mono (by simp)

/-- `basePruned` is nondecreasing on `[10, ∞)`: its derivative is
`ln 3 - (1/2) ln(1 - 1/c) ≥ 0`. -/
theorem basePruned_monotoneOn : MonotoneOn basePruned (Ici 10) := by
  have hder : ∀ c : ℝ, 10 < c →
      HasDerivAt (fun c => 1 / 2 * cEntropy c + (c - 1) * log 3)
        _ c := fun c hc =>
    ((hasDerivAt_cEntropy).const_mul _).add
      (((hasDerivAt_id c).sub_const 1).mul_const (log 3))
  have key : MonotoneOn (fun c => 1 / 2 * cEntropy c + (c - 1) * log 3) (Ici 10) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 10)
    · have := continuous_cEntropy
      fun_prop
    · intro c hc
      rw [interior_Ici] at hc
      exact (hder c hc).differentiableAt.differentiableWithinAt
    · intro c hc
      rw [interior_Ici] at hc
      rw [(hder c hc).deriv]
      have h2 : log (c - 1) ≤ log c := by grind [log_le_log]
      positivity
  intro x hx y hy hxy
  have hx1 : 1 < x := by grind
  have hy1 : 1 < y := by linarith
  rw [basePruned_eq hx1, basePruned_eq hy1]
  aesop
