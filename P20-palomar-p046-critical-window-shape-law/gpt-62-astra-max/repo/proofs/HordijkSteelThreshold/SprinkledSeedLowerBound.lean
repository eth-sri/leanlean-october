module

public import proofs.HordijkSteelThreshold.InfiniteSprinklingLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory unitInterval Filter
open scoped ENNReal

noncomputable def staticSurvival (a : I) : ENNReal :=
  infiniteStaticMeasure a {field | ReversibleUnbounded 2 field}

end HordijkSteelThreshold
