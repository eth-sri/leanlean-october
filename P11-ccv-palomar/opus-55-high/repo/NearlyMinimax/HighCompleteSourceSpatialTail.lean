module

public import NearlyMinimax.HighCompleteSourceFrameTail
public import RoughRegime.Macro
public import NearlyMinimax.HighMarkedMeasurable
public import NearlyMinimax.HighSelectedScoreEnergy
public import NearlyMinimax.AliasTailSummation
public import NearlyMinimax.CardinalProductDesign
public import RoughRegime.Notation

𝗌

/-! Genuine spatial and factorial large-count bounds for the complete
canonical source. The raw uniform cap is proved from actual packet total
variation, and all response/spatial integrations are derived here. -/
𝚫
𝚪
𝚨
𝚩
𝛆
𝚬

theorem fullSpatialPatchDesign_real_univ d n :
    (𝖮₁).real univ = 2 ^(d*n) := by
  simp only [fullSpatialPatchDesign, measureReal_def, Measure.pi_univ,
    Measure.restrict_apply_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_pow]
  change 𝗮₁^n = _
  rw [spatialPatchBox_real_volume, pow_mul]
