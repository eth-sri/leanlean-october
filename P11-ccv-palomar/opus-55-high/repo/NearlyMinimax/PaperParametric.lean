module

public import NearlyMinimax.ProjectionUpper
public import NearlyMinimax.ParametricLower
public import NearlyMinimax.PaperGoals
public import RoughRegime.Notation

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace NearlyMinimax

/-- Manuscript `thm:parametric`, proved against the original statistical
class by combining the actual projection estimator and constructed
ternary two-point submodel. -/
theorem paper_parametric (C : ModelConstants d) : ParametricClaim C := by
  intro hs hparametric
  obtain ⟨c, hc, hlower⟩ := parametric_minimax_lower C
  let A := max (Real.sqrt $ 2 * projectionUpperConstant C ) $ max 1 c⁻¹
  have hA : 𝘪 := lt_of_lt_of_le  𝖠₄  $ (le_max_left 1 c⁻¹).trans $ le_max_right ..
  have hAc : A⁻¹ ≤ c := by
    calc
      A⁻¹ ≤ c⁻¹ ⁻¹ := (inv_le_inv₀ hA $ inv_pos.mpr hc ).mpr $ (le_max_right 1 c⁻¹).trans $ le_max_right ..
      _ = c := inv_inv c
  refine ⟨A, hA, ?_⟩
  intro n hn
  have hscale := Real.rpow_nonneg (Nat.cast_nonneg n) $ -𝙖
  constructor
  · exact (ENNReal.ofReal_le_ofReal $ mul_le_mul_of_nonneg_right hAc hscale ).trans $ hlower n hn
  · exact (minimax_rms_projection_parametric_upper C  𝖡₃  hparametric).trans
      $ ENNReal.ofReal_le_ofReal $ mul_le_mul_of_nonneg_right (le_max_left ..) hscale
