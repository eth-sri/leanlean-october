module
public import RetunedSmoothDetector
public import MathCollab.Density.Stronger.ShortPoweredHeight

@[expose] public section

open Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

/-- Original smooth scale, half choice, and Taylor index: all chosen from a
finite set before the zero. -/
def smoothTaylorIndices (a T : ℝ) : Finset (ℤ × ℕ × ℕ) :=
  (smoothScaleIndices (detectorY a T*(Real.log T)^2)).product
    ((Finset.range 2).product (Finset.range (detectorTaylorCutoff T+1)))

def smoothTaylorMember (a δ T : ℝ) (p : ℤ × ℕ × ℕ) (t : ℝ) : ℂ :=
  genericTaylorPolynomial
    (smoothShortCoefficient (detectorX δ T) (detectorY a T) ((2 : ℝ)^p.1))
    (smoothHalfScale p.1 p.2.1) p.2.2 t





