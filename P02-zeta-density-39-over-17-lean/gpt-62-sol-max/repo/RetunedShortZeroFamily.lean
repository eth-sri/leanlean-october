module
public import RetunedLongMeanCover
public import MathCollab.Density.LocalZeroCount

@[expose] public section

open Real Complex Filter MeasureTheory Finset Set
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

/-- The actual analytic-multiplicity subset detected by the retuned short family. -/
def smoothShortZeroFinset (η σ a δ T : ℝ) : Finset ℂ := by
  classical
  exact (zetaZeroFinset σ T (2*T)).filter (fun ρ =>
    ∃ q ∈ smoothPoweredIndices a δ T,
      (smoothPoweredFamilyScale q:ℝ)^σ*T^(-2*η) ≤
        ‖detectingPolynomial (smoothPoweredFamilyScale q)
          (smoothPoweredFamilyCoefficient η a δ T q) ρ.im‖)

def smoothShortZeroCount (η σ a δ T : ℝ) : ℕ :=
  ∑ ρ ∈ smoothShortZeroFinset η σ a δ T, zetaMultiplicity ρ

theorem smoothShortZeroFinset_subset (η σ a δ T : ℝ) :
    smoothShortZeroFinset η σ a δ T ⊆ zetaZeroFinset σ T (2*T) := by
  classical
  exact filter_subset _ _

end Montgomery.RationalMoment.RightDetector
