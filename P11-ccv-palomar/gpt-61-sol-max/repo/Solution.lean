module

public import NearlyMinimax.PaperMain
public import NearlyMinimax.PaperLowSmoothness
public import NearlyMinimax.PaperParametric

public section

/-!
# Proved counterparts of the submission statements

These statements repeat the independently readable Challenge verbatim.
Each proof uses the development’s established statistical endpoint. Comparator compares the complete statement-definition closure,
including the concrete model and risk definitions, with no definition holes.
-/

noncomputable section
open Filter
open scoped ENNReal Topology

namespace NearlyMinimax.Submission

variable {d : ℕ} (C : ModelConstants d)
include C

/-- Theorem 1.1: the near-matching lower and upper bounds in the regime
`1 < s < d/4`; constants and threshold are uniform over extension domains. -/
theorem paper_main :
    highSmoothnessRegime C →
      ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
        ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n →
          ENNReal.ofReal (c * paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n ∧
          minimaxRMS (C.withDomain U) n ≤
            ENNReal.ofReal (A * paperRiskScale C n * (Real.log n) ^ paperLogGap C) :=
  NearlyMinimax.paper_main C

/-- Corollary 1.2: the root-mean-square minimax exponent equals `2(s+1)/(d+4)`. -/
alias exponent_limit := NearlyMinimax.paper_exponent_limit

/-- Corollary 1.2: eventual polynomial brackets for every positive epsilon.
The two constants precede epsilon; the eventual threshold can depend on it. -/
alias polynomial_bounds := NearlyMinimax.paper_polynomial_bounds

/-- Theorem 1.3: for `0 < s ≤ 1`, the maximum of the parametric and
nonparametric RMS scales brackets minimax RMS for every `n ≥ 1`. -/
theorem low_smoothness :
    C.smoothness ≤ 1 → ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (A⁻¹ * lowSmoothnessScale C.smoothness d n) ≤ minimaxRMS C n ∧
      minimaxRMS C n ≤ ENNReal.ofReal (A * lowSmoothnessScale C.smoothness d n) :=
  NearlyMinimax.paper_low_smoothness C

/-- Theorem 1.4: for `s > 1` and `d ≤ 4s`, parametric RMS brackets hold
for every `n ≥ 1`, including the boundary `d = 4s`. -/
theorem parametric :
    1 < C.smoothness → (d : ℝ) ≤ 4 * C.smoothness →
      ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
        ENNReal.ofReal (A⁻¹ * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ minimaxRMS C n ∧
        minimaxRMS C n ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-(1 / 2 : ℝ))) :=
  NearlyMinimax.paper_parametric C

end NearlyMinimax.Submission
