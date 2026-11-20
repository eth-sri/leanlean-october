module
public import TwoTermLargeValues
public import DensityDetectorWindows
public import DetectorDensityAssembly

@[expose] public section
open MathCollab.Density

namespace Montgomery.RationalMoment

/-- First detector window. -/
theorem two_term_density_first {σ ε : ℝ}
    (hσ : 12/17 ≤ σ) (hσ' : σ ≤ 5/7) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(6*(1-σ)/(8*σ-3)+ε) :=
  let hw := two_term_window_first σ hσ hσ'
  density_of_window_large_values hw.sigma_low (by linarith [hw.a_low]) hw.a_high
    (by linarith [hw.p_low]) (by linarith [hw.typeII]) hε (fun _ => two_term_full_window_large_values hw)

end Montgomery.RationalMoment
