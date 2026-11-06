module
public import RetunedShortZeroCount
public import MathCollab.Density.Stronger.LongMeanCounting

@[expose] public section

open Real Complex Set Filter MeasureTheory
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

def smoothLongZeroFinset (η σ a δ T : ℝ) : Finset ℂ :=
  zetaZeroFinset σ T (2*T) \ smoothShortZeroFinset η σ a δ T

def smoothLongZeroCount (η σ a δ T : ℝ) : ℕ :=
  ∑ ρ ∈ smoothLongZeroFinset η σ a δ T, zetaMultiplicity ρ

