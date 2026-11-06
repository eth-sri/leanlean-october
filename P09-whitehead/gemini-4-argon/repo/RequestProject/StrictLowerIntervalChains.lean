module

public import RequestProject.StrictTopConeThreeChains

@[expose] public section

/-! Actual chains in strict lower intervals and their cone fillings. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def strictLowerIncl (c : P) : Hom (strictOrderCx (Set.Iio c)) (strictOrderCx P) :=
  strictOrderCxMap Subtype.val (fun _ _ h => h)
