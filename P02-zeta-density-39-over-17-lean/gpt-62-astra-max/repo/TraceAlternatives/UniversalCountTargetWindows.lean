module
public import TraceAlternatives.UniversalCountBudgets

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment





def universalLowMargin (σ a x : ℝ) : ℝ :=
  3*a*(1-σ)/2-1/2+(5*σ-7/2)*x



end Montgomery.RationalMoment
