module
public import GuthMaynard.Improvement.ShortDetectorContour
public import GuthMaynard.Improvement.ShortDetectorEstimates
public import MathCollab.Density.DetectorIdentity

@[expose] public section

open Complex MeasureTheory Set Filter
open MathCollab.Density MathCollab.Density.Contour
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

theorem short_smoothedDetector_contour_identity {ρ : ℂ} {X Y : ℝ}
    (hY : 1 ≤ Y) (hβ : 9/13 ≤ ρ.re) (hβ' : ρ.re < 1)
    (hZero : riemannZeta ρ = 0) :
    smoothedDetector ρ X (1/Y) = detectorResidue ρ X Y +
      (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        detectorKernel ρ X Y (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) :=
  smoothedDetector_contour_identity hY hβ hβ' hZero

end GuthMaynard.Improvement
