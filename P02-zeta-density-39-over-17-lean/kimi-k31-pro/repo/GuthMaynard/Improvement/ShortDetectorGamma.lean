module
public import MathCollab.Density.DetectorGamma

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

theorem short_detector_gamma_bound {a : ℝ} (ha : 0 < a) (hahi : a ≤ 1/2) (u : ℝ) :
    ‖Complex.Gamma (((-a:ℝ):ℂ)+(u:ℂ)*Complex.I)‖ ≤
      (12/a)*(1+|u|)*Real.exp (-|u|) :=
  MathCollab.Density.detector_gamma_bound ha hahi u

end GuthMaynard.Improvement
