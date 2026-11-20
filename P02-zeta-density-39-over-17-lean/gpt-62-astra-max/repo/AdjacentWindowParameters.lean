module
public import AdjacentWindow
public import DensityStrip.Budgets

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Montgomery.RationalMoment

/-- All endpoints and length-window budgets for the second two-term branch. -/
theorem adjacent_window_second (s : ℝ) (hl : (5/7:ℝ) ≤ s) (hr : s ≤ (113/153:ℝ)) :
    AdjacentWindow s (4/(9*s-1)) (12*(1-s)/(9*s-1)) ((21*s-13)/((9*s-1)*(2*s-1))) := by
  set D := 9*s-1
  set E := 2*s-1
  have hD : 0 < D := by dsimp [D]; linarith
  have hE : 0 < E := by dsimp [E]; linarith
  constructor
  all_goals first | linarith | (field_simp [hD,hE]; (try dsimp only [D,E]) <;> first | (ring; done) | quadratic_on hl, hr)

end Montgomery.RationalMoment
