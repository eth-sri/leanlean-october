module

public import RequestProject.StrictThreeBoundarySquared

@[expose] public section

/-! Actual chains in strict lower intervals and their cone fillings. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P : Type u} [PartialOrder P]

def strictLowerIncl (c : P) : Hom (strictOrderCx (Set.Iio c)) (strictOrderCx P) :=
  strictOrderCxMap Subtype.val (fun _ _ h => h)

end FiniteChains.Comb
