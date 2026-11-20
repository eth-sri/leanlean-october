module

public import NearlyMinimax.FinePairRowFacts
public import NearlyMinimax.FinePairRowMass
public import NearlyMinimax.FinePairMatrixPositivity

@[expose] public section

/-! Actual source parameter guards make all three fine-pair reference
rows nondegenerate. No probability or positive-mass premise is supplied. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem finePairRowMass_positive (d : ℕ) [NeZero d] (D : ℕ) (hD : 3 ≤ D)
    (M q : ℕ) (hq : 1 ≤ q) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (C : ℝ) (hC : 0 < C) (T₀ N : ℝ) (hT₀ : 0 < T₀) (hTN : T₀ < N)
    (i : FinePairRowTag) : 0 < finePairRowMass d D M q a b C T₀ N i := by
  have hr :=
    lt_of_lt_of_le zero_lt_one (response_absolute_cost_ge_one q hq)
  have hc : 0 < 2*C^2 := mul_pos (by norm_num) (pow_pos hC _)
  have ho := ordinary_density_absolute_cost_pos a b ha hab D
  have hf := fine_density_absolute_cost_pos a b ha hab M
  have hA₀ := finePairUnitMatrix_l1_pos d D
  have hA₁ := finePairDistanceMatrix_l1_pos d D hD
  cases i
  · rw [finePairRowMass_unit]
    exact mul_pos (mul_pos (mul_pos ho hr) hc) hA₀
  · rw [finePairRowMass_coarse d D M q a b C T₀ N hT₀.le]
    exact mul_pos (mul_pos (mul_pos ho hr) hc) (mul_pos hA₁ (by positivity))
  · rw [finePairRowMass_fine d D M q a b C T₀ N hT₀.le hTN.le]
    have hp : 0 < (N^2-T₀^2)/2 := by nlinarith
    exact mul_pos (mul_pos (mul_pos hf hr) hc) (mul_pos hA₁ hp)

end NearlyMinimax
