module
public import ThirdWindow
public import DensityStrip.Budgets

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Montgomery.RationalMoment

/-- Every exponent and detecting length for the full third orange segment. -/
theorem third_window_parameters (s : ℝ) (hl : (113/153:ℝ) ≤ s) (hr : s ≤ (3/4:ℝ)) :
    ThirdWindow s (85/(153*s+7)) (255*(1-s)/(153*s+7)) ((408*s-248)/((153*s+7)*(2*s-1))) := by
  set D := 153*s+7
  set E := 2*s-1
  have hD : 0 < D := by dsimp [D]; linarith
  have hE : 0 < E := by dsimp [E]; linarith
  constructor
  case budgets =>
    intro x hx hx'
    dsimp only [thirdAmplifierExponent]
    simp only [max_le_iff]
    repeat' apply And.intro
    all_goals revert x; apply DensityStrip.affine_window <;> try dsimp only
    all_goals try (intro; ring; done)
    all_goals field_simp [hD,hE]; (try dsimp only [D,E]) <;> quadratic_on hl, hr
  all_goals first | linarith | (field_simp [hD,hE]; (try dsimp only [D,E]) <;> first | (ring; done) | quadratic_on hl, hr)

end Montgomery.RationalMoment
