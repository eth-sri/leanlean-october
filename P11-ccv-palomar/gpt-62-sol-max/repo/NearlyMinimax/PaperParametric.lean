module

public import NearlyMinimax.ProjectionUpper
public import NearlyMinimax.ParametricLower
public import NearlyMinimax.PaperGoals

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace NearlyMinimax

/-- Manuscript `thm:parametric`, proved against the original statistical
class by combining the actual projection estimator and constructed
ternary two-point submodel. -/
theorem paper_parametric {d : ℕ} (C : ModelConstants d) : ParametricClaim C := by
  intro hs hparametric
  obtain ⟨c, hc, hlower⟩ := parametric_minimax_lower C
  let A := max (Real.sqrt (2 * projectionUpperConstant C)) (max 1 c⁻¹)
  have hA1 : (1 : ℝ) ≤ A := (le_max_left 1 c⁻¹).trans (le_max_right _ _)
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  have hAcinv : c⁻¹ ≤ A := (le_max_right 1 c⁻¹).trans (le_max_right _ _)
  have hAupper : Real.sqrt (2 * projectionUpperConstant C) ≤ A := le_max_left _ _
  have hAc : A⁻¹ ≤ c := by
    calc
      A⁻¹ ≤ (c⁻¹)⁻¹ := (inv_le_inv₀ hA (inv_pos.mpr hc)).mpr hAcinv
      _ = c := inv_inv c
  refine ⟨A, hA, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hscale := Real.rpow_nonneg hn0 (-(1 / 2 : ℝ))
  constructor
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAc hscale)).trans (hlower n hn)
  · exact (minimax_rms_projection_parametric_upper C (by omega) hparametric).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAupper hscale))

end NearlyMinimax
