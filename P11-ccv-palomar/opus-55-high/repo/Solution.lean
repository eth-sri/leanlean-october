module

public import NearlyMinimax.PaperMain
public import NearlyMinimax.PaperLowSmoothness
public import NearlyMinimax.PaperParametric

public section

/-!
# Proved counterparts of the submission statements

These statements repeat the independently readable Challenge verbatim.
The `change` steps verify definitional equality with the development's
proposition-valued targets; each proof then uses its established statistical
endpoint. Comparator compares the complete statement-definition closure,
including the concrete model and risk definitions, with no definition holes.
-/

noncomputable section
open Filter
open scoped ENNReal Topology

namespace NearlyMinimax.Submission

/-- Theorem 1.1: the near-matching lower and upper bounds in the regime
`1 < s < d/4`; constants and threshold are uniform over extension domains. -/
theorem paper_main {d } C :
    highSmoothnessRegime C →
      ∃ c A , 0 < c ∧ 0 < A ∧ ∃ n₀ , 2 ≤ n₀ ∧
        ∀ (U : ExtensionDomain d) n, n₀ ≤ n →
          ENNReal.ofReal (c * paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n ∧
          minimaxRMS (C.withDomain U) n ≤
            ENNReal.ofReal (A * paperRiskScale C n * (Real.log n) ^ paperLogGap C) := by
  exact NearlyMinimax.paper_main C

set_option hygiene false
local notation "𝔄" => minimaxRMS C n
section

variable {d }
    (C : ModelConstants d)

/-- Corollary 1.2: the root-mean-square minimax exponent equals `2(s+1)/(d+4)`. -/
theorem exponent_limit (hreg : highSmoothnessRegime C) :
    Tendsto (fun n  => -Real.log (𝔄).toReal / Real.log n)
      atTop (𝓝 (rateExponent C.smoothness d)) := NearlyMinimax.paper_exponent_limit C hreg

/-- Corollary 1.2: eventual polynomial brackets for every positive epsilon.
The two constants precede epsilon; the eventual threshold can depend on it. -/
theorem polynomial_bounds (hreg : highSmoothnessRegime C) :
    ∃ c A , 0 < c ∧ 0 < A ∧ ∀ epsilon , 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        c * n ^ (-rateExponent C.smoothness d - epsilon) ≤ (𝔄).toReal ∧
        (𝔄).toReal ≤ A * n ^ (-rateExponent C.smoothness d) := NearlyMinimax.paper_polynomial_bounds C hreg

/-- Theorem 1.3: for `0 < s ≤ 1`, the maximum of the parametric and
nonparametric RMS scales brackets minimax RMS for every `n ≥ 1`. -/
theorem low_smoothness :
    C.smoothness ≤ 1 → ∃ A , 0 < A ∧ ∀ n , 1 ≤ n →
      ENNReal.ofReal (A⁻¹ * lowSmoothnessScale C.smoothness d n) ≤ 𝔄 ∧
      𝔄 ≤ ENNReal.ofReal (A * lowSmoothnessScale C.smoothness d n) := by
  exact NearlyMinimax.paper_low_smoothness C

end

set_option hygiene false
local notation "𝔅" => n ^ (-(1 / 2 : ℝ))
/-- Theorem 1.4: for `s > 1` and `d ≤ 4s`, parametric RMS brackets hold
for every `n ≥ 1`, including the boundary `d = 4s`. -/
theorem parametric {d } (C : ModelConstants d) :
    1 < C.smoothness → d ≤ 4 * C.smoothness →
      ∃ A , 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
        ENNReal.ofReal (A⁻¹ * 𝔅) ≤ 𝔄 ∧
        𝔄 ≤ ENNReal.ofReal (A * 𝔅) := by
  exact NearlyMinimax.paper_parametric C

end NearlyMinimax.Submission
