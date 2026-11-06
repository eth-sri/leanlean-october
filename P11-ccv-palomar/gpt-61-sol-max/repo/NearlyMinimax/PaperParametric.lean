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
theorem paper_parametric {d } (C : ModelConstants d) : ParametricClaim C := by
  intro hs hparametric
  obtain ⟨c, hc, hlower⟩ := parametric_minimax_lower C
  obtain ⟨A, hA, hAc, hAu⟩ := exists_pos_upper_with_inv_le hc (Real.sqrt (2 * projectionUpperConstant C))
  refine ⟨A, hA, fun n hn => ?_⟩
  have hscale : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  exact ⟨(ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAc hscale)).trans (hlower n hn),
    (minimax_rms_projection_parametric_upper C (by omega) hparametric).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAu hscale))⟩

end NearlyMinimax
