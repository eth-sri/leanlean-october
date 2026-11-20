module
/- Adapted from the audited MathCollab.Density.DetectorIdentity at
 eff263d7b957f99e73fd226f84b83dd826941151. Only the independently proved
 lower-real-part components are substituted; the literal detector is preserved. -/
public import GuthMaynard.Improvement.ShortDetectorContour
public import GuthMaynard.Improvement.ShortDetectorEstimates
public import MathCollab.Density.DetectorIdentity

@[expose] public section

open Complex MeasureTheory Set Filter MathCollab.Density MathCollab.Density.Contour
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- The exact infinite contour identity, with no Weyl premise or fixed relation
between the independent mollifier and smoothing parameters. -/
theorem short_smoothedDetector_contour_identity {ρ : ℂ} {X Y : ℝ}
    (hY : 1 ≤ Y) (hβ : 9/13 ≤ ρ.re) (hβ' : ρ.re < 1)
    (hZero : riemannZeta ρ = 0) :
    smoothedDetector ρ X (1/Y) = detectorResidue ρ X Y +
      (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        detectorKernel ρ X Y (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) :=
  smoothedDetector_contour_identity_of_half_lt hY (by linarith) hβ' hZero

end GuthMaynard.Improvement
