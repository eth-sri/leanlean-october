module
public import LaterPairs.PhysicalLongMeanCover
public import RetunedLongMultiplicity
public import RetunedShortZeroCount
public import MathCollab.Density.Stronger.LongMeanCounting
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Real Complex Set Filter MeasureTheory
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density

/- Actual slab zeros outside the already counted short family. -/
/- The complementary part keeps the original analytic multiplicity. -/
export Montgomery.RationalMoment.RightDetector (smooth_zeroCount_partition smoothLongZeroFinset_subset)

/- Exact partition of every actual slab zero and all its analytic multiplicity. -/

/- One critical-mean constant precedes the height and every complementary zero. -/
theorem smoothLongZeroFinset_eventually_detects_mean {σ a δ η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hδ : 0 < δ) (hδ' : δ ≤ 1/8) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ ρ ∈ smoothLongZeroFinset η σ a δ T,
      (detectorY a T)^((σ-1/2)/2) ≤
        48*C*Real.sqrt (detectorX δ T)*Real.log T*weightedCriticalMean 128 ρ.im := by
  obtain ⟨C, hC, hcover⟩ := smooth_long_mean_or_short_powered_cover hw hδ hδ' hη 128 (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ), hcover] with T hT hc
  pm_381 ρ hρ hzmem hnot Finset.mem_sdiff.mp
  pm_269 hz hβ hγ hγ' mem_zetaZeroFinset.mp hzmem
  have habs : |ρ.im| = ρ.im := abs_of_nonneg (hT.trans hγ)
  rcases hc ρ hβ hz.2.2 (by rwa [habs]) (by rwa [habs]) hz.1 with hmean | hshort
  · exact hmean
  · exact False.elim (hnot (Finset.mem_filter.mpr ⟨hzmem, hshort⟩))

/- Unconditional restoration of the complementary analytic-multiplicity count
from separated long detectors. The right side is the literal physical twelfth
moment, not a supplied moment bound. -/

end Montgomery.RationalMoment.RightDetector.Physical
