module

public import NearlyMinimax.FinePairRowFacts
public import RoughRegime.Macro
public import NearlyMinimax.FinePairRowMass
public import NearlyMinimax.FinePairMatrixPositivity
public import RoughRegime.Notation

𝗍

/-! Actual source parameter guards make all three fine-pair reference
rows nondegenerate. No probability or positive-mass premise is supplied. -/
𝚫
𝚪
𝚨
𝚩
𝚰

theorem finePairRowMass_positive (d : ℕ) [NeZero d] (D : ℕ) (hD : 𝗕)
    (M q : ℕ) (hq : 𝗘) (a b : ℝ) (ha : 𝙆) (hab : 𝙭)
    (C : ℝ) (hC : 𝙴) (T₀ N : ℝ) (hT₀ : 0 < T₀) (hTN : T₀ < N)
    (i : FinePairRowTag) : 0 < finePairRowMass d D M q a b C T₀ N i := by
  have hr :=
    lt_of_lt_of_le zero_lt_one $ response_absolute_cost_ge_one q hq
  have ho := ordinary_density_absolute_cost_pos a b ha hab D
  have hf := fine_density_absolute_cost_pos a b ha hab M
  have hA₀ := finePairUnitMatrix_l1_pos d D
  have hA₁ := finePairDistanceMatrix_l1_pos d D hD
  cases i
  · rw [finePairRowMass_unit]
    positivity
  · rw [finePairRowMass_coarse d D M q a b C T₀ N hT₀.le]
    positivity
  · rw [finePairRowMass_fine d D M q a b C T₀ N hT₀.le hTN.le]
    bound
