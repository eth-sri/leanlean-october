module
public import RetunedShortZeroCount
public import MathCollab.Density.Stronger.LongMeanCounting
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Real Complex Set Filter MeasureTheory
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

/-- Actual slab zeros outside the already counted short family. -/
def smoothLongZeroFinset (η σ a δ T : ℝ) : Finset ℂ :=
  zetaZeroFinset σ T (2*T) \ smoothShortZeroFinset η σ a δ T

/-- The complementary part keeps the original analytic multiplicity. -/
def smoothLongZeroCount (η σ a δ T : ℝ) : ℕ :=
  ∑ ρ ∈ smoothLongZeroFinset η σ a δ T, zetaMultiplicity ρ

theorem smoothLongZeroFinset_subset (η σ a δ T : ℝ) :
    smoothLongZeroFinset η σ a δ T ⊆ zetaZeroFinset σ T (2*T) := Finset.sdiff_subset

/-- Exact partition of every actual slab zero and all its analytic multiplicity. -/
theorem smooth_zeroCount_partition (η σ a δ T : ℝ) :
    zetaSlabCount σ T (2*T) = smoothShortZeroCount η σ a δ T + smoothLongZeroCount η σ a δ T := by
  unfold zetaSlabCount smoothShortZeroCount smoothLongZeroCount smoothLongZeroFinset
  have hs := Finset.sum_sdiff (smoothShortZeroFinset_subset η σ a δ T)
    (f := zetaMultiplicity)
  omega

/-- One critical-mean constant precedes the height and every complementary zero. -/
theorem smoothLongZeroFinset_eventually_detects_mean {σ a δ η : ℝ}
    (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ) (hδ : 0 < δ) (hδ' : δ ≤ 1/8) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ ρ ∈ smoothLongZeroFinset η σ a δ T,
      (detectorY a T)^((σ-1/2)/2) ≤
        48*C*Real.sqrt (detectorX δ T)*Real.log T*weightedCriticalMean 128 ρ.im := by pm_4457 hw hsigma

end Montgomery.RationalMoment.RightDetector
