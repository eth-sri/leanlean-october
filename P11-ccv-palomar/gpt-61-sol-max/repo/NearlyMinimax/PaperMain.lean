module

public import NearlyMinimax.PaperLowerSharp
public import NearlyMinimax.PaperSharpUpper
public import NearlyMinimax.PaperCorollaries
public import NearlyMinimax.NatRateConsequences

@[expose] public section

/-! The paper's main bracket and unconditional asymptotic consequences.
The statistical upper and lower bounds used here are proved for the original
model, with constants uniform over the open extension domain. -/

noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax

section
variable {d : ℕ} (C : ModelConstants d)

theorem paper_main  : MainBracketClaim C :=
  mainBracketClaim_of_separate_bounds C (paper_upper_sharp C) (paper_lower_sharp C)

section
variable (hreg : highSmoothnessRegime C)
include hreg

theorem paper_exponent_limit 
     :
    Tendsto (fun n  => -Real.log (minimaxRMS C n).toReal / Real.log n)
      atTop (𝓝 (rateExponent C.smoothness d)) :=
  paper_exponent_limit_of_mainBracketClaim C hreg (paper_main C)

theorem paper_polynomial_bounds 
     :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ epsilon , 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        c*n^(-rateExponent C.smoothness d-epsilon) ≤ (minimaxRMS C n).toReal ∧
        (minimaxRMS C n).toReal ≤ A*n^(-rateExponent C.smoothness d) :=
  polynomial_bounds_nat_of_rateBracket (paper_stretchConstant_pos C hreg)
    (hasNatRateBracket_of_mainBracketClaim C hreg (paper_main C))
end

end


end NearlyMinimax
