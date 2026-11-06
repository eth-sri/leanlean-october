module

public import NearlyMinimax.HighCardinalRawEnvelope
public import RoughRegime.Macro
public import NearlyMinimax.FinePairSpatialEnergy
public import RoughRegime.Notation

𝗌

/-! Full spatial energy of the genuine matched cardinal packet numerator.
The two deterministic envelopes are integrated against the actual Q^n law. -/
𝚫
𝚪
𝚨
𝚩
𝚭

 def cardinalRawSpatialEnergyBudget (d n q : ℕ) (bd C a ρ η T : ℝ) : ℝ :=
  𝗶₂ *
      (𝙒^2 * 𝙉^d * cardinalDefectSquareBudget d n T) +
    𝘔₁ *
      (𝙒^2 * 𝙉^d *
        ((100*𝙊)^2*16*spatialScaleIntegralConstant d)^𝗈)
