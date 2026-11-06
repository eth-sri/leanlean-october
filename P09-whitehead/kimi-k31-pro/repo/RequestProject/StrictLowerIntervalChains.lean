module

public import RequestProject.Oriented

public import RequestProject.StrictThreeBoundarySquared

@[expose] public section

backwardOptions



/-! Actual chains in strict lower intervals and their cone fillings. -/

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def strictLowerIncl (c : P) : Hom (strictOrderCx (Set.Iio c)) (strictOrderCx P) :=
  strictOrderCxMap Subtype.val (fun _ _ h => h)

end FiniteChains.Comb
