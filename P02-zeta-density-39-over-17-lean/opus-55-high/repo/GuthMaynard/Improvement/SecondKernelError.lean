module
public import GuthMaynard.Improvement.PoissonTails

public section
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace GuthMaynard.Improvement

theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp]

end GuthMaynard.Improvement
