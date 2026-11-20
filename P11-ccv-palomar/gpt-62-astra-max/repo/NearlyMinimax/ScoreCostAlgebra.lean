module

public import NearlyMinimax.PaperScorePath

@[expose] public section

/-! The scalar passage from the full score energy and update cost to the
manuscript's quantitative lower bound. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax

def localScorePathLength (c B I : ℝ) : ℝ := c / (1 + B + I)

variable {c B I η score : ℝ} (hc : 0 < c) (hB : 0 ≤ B) (hI : 0 ≤ I)

include hc hB hI in
theorem localScorePathLength_pos : 0 < localScorePathLength c B I := div_pos hc (by positivity)

theorem localScorePathLength_energy_le (hc : 0 ≤ c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) : localScorePathLength c B I * I ≤ c := by
  rw [localScorePathLength, div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity)).mpr
  bound

theorem three_term_square_le (B I : ℝ) :
    (1 + B + I) ^ 2 ≤ 3 * (1 + B ^ 2 + I ^ 2) := by
  nlinarith only [sq_nonneg (1 - B), sq_nonneg (1 - I), sq_nonneg (B - I)]

include hc hB hI in
theorem score_cost_numeric (hscore0 : 0 ≤ score)
    (hscore : score ≤ localScorePathLength c B I * I) :
    let scale := 3 * (2 + c) ^ 2
    c ^ 2 / (scale) * η ^ 4 / (1 + B ^ 2 + I ^ 2) ≤
      η ^ 4 * (localScorePathLength c B I) ^ 2 / (2 + score) ^ 2 := by
  intro scale
  have hsc  := hscore.trans (localScorePathLength_energy_le hc.le hB hI)
  have hsq : (2 + score) ^ 2 ≤ (2 + c) ^ 2 := by
    bound
  have hprod : (2 + score) ^ 2 * (1 + B + I) ^ 2 ≤
      scale * (1 + B ^ 2 + I ^ 2) := by
    calc
      _ ≤ _ :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left (three_term_square_le B I) (sq_nonneg _)
      _ = _ := by ring
  have hfrac : (c ^ 2 * η ^ 4) /
      (scale * (1 + B ^ 2 + I ^ 2)) ≤
      (c ^ 2 * η ^ 4) / ((2 + score) ^ 2 * (1 + B + I) ^ 2) := by
    gcongr
  calc
    _ = _ := by
      field_simp <;> ring
    _ ≤ _ := hfrac
    _ = _ := by
      rw [localScorePathLength]
      field_simp <;> ring

end NearlyMinimax
