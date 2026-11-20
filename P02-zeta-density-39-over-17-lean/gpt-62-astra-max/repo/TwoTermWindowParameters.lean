module
public import DensityWindowBudgets
public import DensityStrip.Budgets

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Montgomery.RationalMoment

/-- All endpoints and length-window budgets for the first two-term branch. -/
theorem two_term_window_first (s : ℝ) (hl : (12/17:ℝ) ≤ s) (hr : s ≤ (5/7:ℝ)) :
    TwoTermWindow s (2/(8*s-3)) (6*(1-s)/(8*s-3)) ((14*s-9)/((8*s-3)*(2*s-1))) := by
  set D := 8*s-3
  set E := 2*s-1
  have hD : 0 < D := by dsimp [D]; linarith
  have hE : 0 < E := by dsimp [E]; linarith
  constructor
  all_goals first | linarith | (field_simp [hD,hE]; (try dsimp only [D,E]) <;> first | (ring; done) | quadratic_on hl, hr)

end Montgomery.RationalMoment
