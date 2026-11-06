module

public import HypoellipticAleksandrov.Parabolic.SobolevGridFTC
public import HypoellipticAleksandrov.Parabolic.FiniteSupportL1L2

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

/- Coordinate iterated derivatives do not enlarge topological support. -/
theorem coordinateIteratedFDeriv_tsupport_subset
    {d } (alpha : TimeVelocityMultiIndex d)
    (f : TimeVelocity d → ℝ) :
    tsupport (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha f) ⊆
      tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  apply support_iteratedFDeriv_subset (f := f) (𝕜 := ℝ) alpha.coordinateList.length
  intro hzero
  exact hz (by
    unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
    rw [hzero]
    exact ContinuousMultilinearMap.zero_apply _)

/- The grid-FTC sup estimate with the exact common compact-support constant. -/
end HypoellipticAleksandrov.Parabolic
