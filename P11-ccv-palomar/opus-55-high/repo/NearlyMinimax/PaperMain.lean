module

public import NearlyMinimax.PaperLowerSharp
public import RoughRegime.Macro
public import NearlyMinimax.PaperSharpUpper
public import NearlyMinimax.PaperCorollaries
public import NearlyMinimax.NatRateConsequences
public import RoughRegime.Notation

𝗍

/-! The paper's main bracket and unconditional asymptotic consequences.
The statistical upper and lower bounds used here are proved for the original
model, with constants uniform over the open extension domain. -/

𝚷
𝚶
𝚨

section

𝛇

theorem paper_main : MainBracketClaim C :=
  mainBracketClaim_of_separate_bounds C (paper_upper_sharp C) $ paper_lower_sharp C

theorem paper_exponent_limit (hreg : highSmoothnessRegime C) :
    Tendsto (fun n => -Real.log (𝚢).toReal / Real.log n)
      atTop $ 𝓝 𝗚₂ :=
  paper_exponent_limit_of_mainBracketClaim C hreg $ paper_main C

theorem paper_polynomial_bounds (hreg : highSmoothnessRegime C) :
    ∃ c A , 𝘝 ∧ 𝘪 ∧ ∀ epsilon , 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        c*n^(-𝗚₂-epsilon) ≤ (𝚢).toReal ∧
        (𝚢).toReal ≤ A*n^(-𝗚₂) :=
  polynomial_bounds_nat_of_rateBracket (paper_stretchConstant_pos C hreg)
    $ hasNatRateBracket_of_mainBracketClaim C hreg $ paper_main C
