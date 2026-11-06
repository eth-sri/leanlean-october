module

public import NearlyMinimax.ElementaryUpper
public import NearlyMinimax.LowSmoothnessLower
public import NearlyMinimax.ParametricLower
public import NearlyMinimax.PaperGoals


@[expose] public section

/-! The complete all-sample-size low-smoothness minimax bracket from the
constructed pair estimator and the actual ternary submodels. -/
noncomputable section
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

section
variable {d n : ℕ} (C : ModelConstants d)

theorem lowSmoothnessScale_eq_root 
    (hd : d ≤ 4 * C.smoothness) (hn : 1 ≤ n) :
    lowSmoothnessScale C.smoothness d n = n ^ (-(1 / 2 : ℝ)) := by
  have hden : 0 < (d : ℝ) + 4 * C.smoothness := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith [C.smoothness_pos]
  have hexp : -(4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)) ≤
      -(1 / 2 : ℝ) := by
    apply neg_le_neg
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1 : ℝ) ≤ n) hexp
  exact max_eq_left hpow

theorem lowSmoothnessScale_eq_nonparametric 
    (hd : 4 * C.smoothness ≤ d) (hn : 1 ≤ n) :
    lowSmoothnessScale C.smoothness d n =
      n ^ (-4 * C.smoothness / (d + 4 * C.smoothness)) := by
  have hden : 0 < (d : ℝ) + 4 * C.smoothness := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith [C.smoothness_pos]
  have hexp : -(1 / 2 : ℝ) ≤ -(4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)) := by
    apply neg_le_neg
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1 : ℝ) ≤ n) hexp
  have he : -(4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)) =
      -4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness) := by ring
  simpa only [lowSmoothnessScale, he] using max_eq_right hpow
end


section
variable {d : ℕ} (C : ModelConstants d)

/-- A genuine lower bound for the maximum of the two low-smoothness rates,
including the critical dimension and n = 1. -/
theorem low_smoothness_max_minimax_lower 
    (hs : C.smoothness ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n , 1 ≤ n →
      ENNReal.ofReal (c * lowSmoothnessScale C.smoothness d n) ≤ minimaxRMS C n := by
  by_cases hd : (d : ℝ) ≤ 4 * C.smoothness
  · obtain ⟨c, hc, hbound⟩ := parametric_minimax_lower C
    grind only [lowSmoothnessScale_eq_root]
  · obtain ⟨c, hc, hbound⟩ := low_smoothness_nonparametric_minimax_lower C hs (le_of_not_ge hd)
    grind only [lowSmoothnessScale_eq_nonparametric]

/-- Manuscript `thm:main2`: both bounds hold for the original statistical
class, with one positive constant for every sample size n ≥ 1. -/
theorem paper_low_smoothness  : LowSmoothnessClaim C := by
  intro hs
  obtain ⟨c, hc, hbound⟩ := low_smoothness_max_minimax_lower C hs
  obtain ⟨A, hA, hAc, hAu⟩ := exists_pos_upper_with_inv_le hc (elementaryRMSConstant C)
  refine ⟨A, hA, fun n hn => ?_⟩
  have hscale : 0 ≤ lowSmoothnessScale C.smoothness d n :=
    (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans (le_max_left _ _)
  constructor
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAc hscale)).trans (hbound n hn)
  · have hupper := (ENNReal.rpow_le_rpow
        (minimaxRisk_le_worstCaseRisk C (elementaryEstimator C n)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
      (elementary_upper_low_smoothness C hs (by omega : 0 < n))
    change minimaxRMS C n ≤ _ at hupper
    have hu : minimaxRMS C n ≤ ENNReal.ofReal
        (elementaryRMSConstant C * lowSmoothnessScale C.smoothness d n) := by
      simpa only [neg_mul, neg_div, lowSmoothnessScale] using hupper
    exact hu.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAu hscale))
end


end NearlyMinimax
