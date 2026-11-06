module

public import NearlyMinimax.DesignCounts
public import RoughRegime.Macro
public import NearlyMinimax.HighObservationLaw
public import NearlyMinimax.HighWindowGeometry
public import RoughRegime.Notation

𝗌

/-! Actual binomial occupancy under the normalized original design law,
and the exact fixed denominator constant used in the high lower score
energy. Raw normalization and patch volume are derived. -/
𝚫
𝚳
𝚨
𝚩
𝚾
𝚬

def highNormalizedDesignLaw (p : 𝙀) : 𝘹₁ :=
  (cubeVolume d).withDensity fun x => ENNReal.ofReal $ highNormalizedDensity p x

theorem high_normalized_design_probability p
    (hp : Measurable p) a b (ha : 𝙆)
    (hb : 𝚃₂) : IsProbabilityMeasure $ highNormalizedDesignLaw p :=
  normalizedDensityTernaryParameter_design_probability p hp a b ha hb

/-- The exact source C_sharp, obtained from one raw density floor and one
normalizing mass floor in the selected likelihood. -/
def highFixedScoreDenominator (pMinus cMass : ℝ) : ℝ := (pMinus ^ 2 * cMass)⁻¹

theorem high_fixed_score_denominator_pos (hp : 0 < pMinus) (hc : 0 < cMass) :
    0 < highFixedScoreDenominator pMinus cMass := by
  unfold highFixedScoreDenominator
  positivity
