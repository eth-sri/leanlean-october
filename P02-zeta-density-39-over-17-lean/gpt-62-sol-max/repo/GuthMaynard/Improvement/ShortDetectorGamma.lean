module
public import MathCollab.Density.DetectorGamma
public import MathCollab.Density.MollifierDirichlet

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace GuthMaynard.Improvement

/-- Correct negative Gamma strip, uniformly on the entire imaginary axis.
The singular dependence on the distance to zero is explicit. -/
theorem short_detector_gamma_bound {a : ℝ} (ha : 0 < a) (hahi : a ≤ 1/2) (u : ℝ) :
    ‖Complex.Gamma (((-a:ℝ):ℂ)+(u:ℂ)*Complex.I)‖ ≤
      (12/a)*(1+|u|)*Real.exp (-|u|) :=
  MathCollab.Density.norm_Gamma_negative_strip ha (by linarith) le_rfl

end GuthMaynard.Improvement
