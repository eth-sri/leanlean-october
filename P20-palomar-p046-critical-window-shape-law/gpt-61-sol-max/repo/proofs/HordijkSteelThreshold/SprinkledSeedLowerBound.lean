
import proofs.HordijkSteelThreshold.RandomBaseSprinkling




namespace HordijkSteelThreshold
open unitInterval

noncomputable def staticSurvival (a : I)  :=
  infiniteStaticMeasure a {field | ReversibleUnbounded 2 field}

end HordijkSteelThreshold
