module

public import NearlyMinimax.PaperLowerSharp
public import NearlyMinimax.PaperSharpUpper
public import NearlyMinimax.PaperCorollaries
public import NearlyMinimax.NatRateConsequences
public import NearlyMinimax.PaperLowSmoothness
public import NearlyMinimax.ProjectionUpper

public section

/-!
# Proved counterparts of the submission statements

The statements use the concrete model and loss of the challenge.  The
bracket combines the statistical endpoints; the two all-sample brackets
use the same positive rescaling lemma.
-/

noncomputable section
open Filter
open scoped ENNReal Topology

namespace NearlyMinimax.Submission

variable {d : ℕ} (C : ModelConstants d)

/-- Theorem 1.1: the near-matching lower and upper bounds in the regime
`1 < s < d/4`; constants and threshold are uniform over extension domains. -/
theorem paper_main :
    highSmoothnessRegime C →
      ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
        ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n →
          ENNReal.ofReal (c * paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n ∧
          minimaxRMS (C.withDomain U) n ≤
            ENNReal.ofReal (A * paperRiskScale C n * (Real.log n) ^ paperLogGap C) :=
  mainBracketClaim_of_separate_bounds C (paper_upper_sharp C) (paper_lower_sharp C)

/-- Corollary 1.2: the root-mean-square minimax exponent equals `2(s+1)/(d+4)`. -/
theorem exponent_limit
    (hreg : highSmoothnessRegime C) :
    Tendsto (fun n : ℕ => -Real.log (minimaxRMS C n).toReal / Real.log (n : ℝ))
      atTop (𝓝 (rateExponent C.smoothness d)) :=
  exponent_limit_nat_of_rateBracket (hasNatRateBracket_of_mainBracketClaim C hreg (paper_main C))

/-- Corollary 1.2: eventual polynomial brackets for every positive epsilon.
The two constants precede epsilon; the eventual threshold can depend on it. -/
theorem polynomial_bounds
    (hreg : highSmoothnessRegime C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        c * (n : ℝ) ^ (-rateExponent C.smoothness d - epsilon) ≤ (minimaxRMS C n).toReal ∧
        (minimaxRMS C n).toReal ≤ A * (n : ℝ) ^ (-rateExponent C.smoothness d) :=
  polynomial_bounds_nat_of_rateBracket (paper_stretchConstant_pos hreg)
    (hasNatRateBracket_of_mainBracketClaim C hreg (paper_main C))

/-- Theorem 1.3: for `0 < s ≤ 1`, the maximum of the parametric and
nonparametric RMS scales brackets minimax RMS for every `n ≥ 1`. -/
theorem low_smoothness :
    C.smoothness ≤ 1 → ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (A⁻¹ * lowSmoothnessScale C.smoothness d n) ≤ minimaxRMS C n ∧
      minimaxRMS C n ≤ ENNReal.ofReal (A * lowSmoothnessScale C.smoothness d n) := by
  intro hs
  refine balance_rate_bounds (b := elementaryRMSConstant C) ?_ (low_smoothness_max_minimax_lower hs) ?_
  · intro n hn
    unfold lowSmoothnessScale
    positivity
  · intro n hn
    apply (ENNReal.rpow_le_rpow (minimaxRisk_le_worstCaseRisk ..)
      (by norm_num)).trans
    simpa only [lowSmoothnessScale, neg_mul, neg_div] using elementary_upper_low_smoothness hs hn

/-- Theorem 1.4: for `s > 1` and `d ≤ 4s`, parametric RMS brackets hold
for every `n ≥ 1`, including the boundary `d = 4s`. -/
theorem parametric :
    1 < C.smoothness → (d : ℝ) ≤ 4 * C.smoothness →
      ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
        ENNReal.ofReal (A⁻¹ * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ minimaxRMS C n ∧
        minimaxRMS C n ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  intro _ hd
  refine balance_rate_bounds ?_ (parametric_minimax_lower C)
    (fun n hn => minimax_rms_projection_parametric_upper hn hd)
  intro n _; positivity

end NearlyMinimax.Submission
