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
  exact uniform_rms_bracket C _ (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hc hlower
    (fun n hn => minimax_rms_projection_parametric_upper C (by omega) hparametric)

end NearlyMinimax
