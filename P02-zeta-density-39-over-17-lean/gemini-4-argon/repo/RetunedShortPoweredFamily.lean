module
public import RetunedShortTaylorCover
public import MathCollab.Density.Stronger.ShortPoweredHeight

@[expose] public section

open Real Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

/-- This bound is fixed by sigma and delta, before T and any zero. -/
def smoothPowerBound (a δ : ℝ) : ℕ := ⌈2*a/δ⌉₊

def smoothPoweredFamilyScale (q : (ℤ × ℕ × ℕ) × ℕ × ℕ) : ℕ :=
  2^q.2.2*(smoothHalfScale q.1.1 q.1.2.1)^q.2.1

/-- The complete finite powered family, restricted by scale conditions that
are independent of the zero. The original smooth scale remains in q.1.1. -/
def smoothPoweredIndices (a δ T : ℝ) : Finset ((ℤ × ℕ × ℕ) × ℕ × ℕ) :=
  ((smoothTaylorIndices a T).product
    ((Finset.Icc 1 (smoothPowerBound a δ)).product (Finset.range (smoothPowerBound a δ)))).filter
    (fun q => q.2.2 < q.2.1 ∧
      T^(a) ≤ (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ∧
      (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ≤ T^(smoothingExponent a))

def smoothPoweredFamilyCoefficient (η a δ T : ℝ) (q : (ℤ × ℕ × ℕ) × ℕ × ℕ) (n : ℕ) : ℂ :=
  normalizedSmoothPoweredCoefficient η T (detectorX δ T) (detectorY a T)
    q.1.1 q.1.2.1 q.1.2.2 q.2.1 n






