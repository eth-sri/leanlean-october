module
public import ThirdLargeValues
public import DensityDetectorWindows
public import DetectorDensityAssembly

@[expose] public section
open MathCollab.Density

namespace Montgomery.RationalMoment

/-- Third detector window. -/
theorem third_density_segment {σ ε : ℝ}
    (hσ : 113/153 ≤ σ) (hσ' : σ ≤ 3/4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(255*(1-σ)/(153*σ+7)+ε) :=
  let hw := third_window_parameters σ hσ hσ'
  density_of_window_large_values hw.sigma_low (by linarith [hw.a_low]) hw.a_high
    (by linarith [hw.p_low]) (by linarith [hw.typeII]) hε (fun _ => third_full_window_large_values hw)

end Montgomery.RationalMoment
