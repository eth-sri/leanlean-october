module

public import NearlyMinimax.PaperScorePath

@[expose] public section

/-! The scalar passage from the full score energy and update cost to the
manuscript's quantitative lower bound. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax

def localScorePathLength (c B I : ℝ) : ℝ := c / (1 + B + I)

variable {c B I : ℝ}

theorem localScorePathLength_pos (hc : 0 < c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) : 0 < localScorePathLength c B I := div_pos hc (by linarith only [hB, hI])

theorem localScorePathLength_energy_le (hc : 0 ≤ c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) : localScorePathLength c B I * I ≤ c := by
  have hden : 0 < 1 + B + I := by linarith only [hB, hI]
  rw [localScorePathLength, div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  exact mul_le_mul_of_nonneg_left (by linarith only [hB]) hc

theorem three_term_square_le (B I : ℝ) :
    (1 + B + I) ^ 2 ≤ 3 * (1 + B ^ 2 + I ^ 2) := by
  nlinarith only [sq_nonneg (1 - B), sq_nonneg (1 - I), sq_nonneg (B - I)]

theorem score_cost_numeric {c B I η score : ℝ} (hc : 0 < c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) (hscore0 : 0 ≤ score)
    (hscore : score ≤ localScorePathLength c B I * I) :
    c ^ 2 / (3 * (2 + c) ^ 2) * η ^ 4 / (1 + B ^ 2 + I ^ 2) ≤
      η ^ 4 * (localScorePathLength c B I) ^ 2 / (2 + score) ^ 2 := by
  have hden : 0 < 1 + B + I := by linarith only [hB, hI]
  have hscpos : 0 < 2 + score := by linarith only [hscore0]
  have hcpos : 0 < 2 + c := by linarith only [hc]
  have hsumpos : 0 < 1 + B ^ 2 + I ^ 2 := by
    positivity
  have hsq : (2 + score) ^ 2 ≤ (2 + c) ^ 2 := by
    nlinarith only [(hscore.trans (localScorePathLength_energy_le hc.le hB hI)), hscpos, hcpos]
  have hprod : (2 + score) ^ 2 * (1 + B + I) ^ 2 ≤
      3 * (2 + c) ^ 2 * (1 + B ^ 2 + I ^ 2) := by
    calc
      _ ≤ (2 + c) ^ 2 * (1 + B + I) ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ ≤ (2 + c) ^ 2 * (3 * (1 + B ^ 2 + I ^ 2)) :=
        mul_le_mul_of_nonneg_left (three_term_square_le B I) (sq_nonneg _)
      _ = _ := by ring
  have hfrac : (c ^ 2 * η ^ 4) /
      (3 * (2 + c) ^ 2 * (1 + B ^ 2 + I ^ 2)) ≤
      (c ^ 2 * η ^ 4) / ((2 + score) ^ 2 * (1 + B + I) ^ 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hprod
  calc
    _ = (c ^ 2 * η ^ 4) / (3 * (2 + c) ^ 2 * (1 + B ^ 2 + I ^ 2)) := by
      field_simp <;> ring
    _ ≤ (c ^ 2 * η ^ 4) / ((2 + score) ^ 2 * (1 + B + I) ^ 2) := hfrac
    _ = _ := by
      rw [localScorePathLength]
      field_simp <;> ring

end NearlyMinimax
