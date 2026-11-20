module
public import AdjacentLargeValues
public import DensityDetectorWindows
public import DetectorDensityAssembly

@[expose] public section
open MathCollab.Density

namespace Montgomery.RationalMoment

/-- Second detector window. -/
theorem adjacent_density_second {σ ε : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 113/153) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(12*(1-σ)/(9*σ-1)+ε) :=
  let hw := adjacent_window_second σ hσ hσ'
  density_of_window_large_values hw.sigma_low (by linarith [hw.a_low]) hw.a_high
    (by linarith [hw.p_low]) (by linarith [hw.typeII]) hε (fun _ => adjacent_full_window_large_values hw)

end Montgomery.RationalMoment
