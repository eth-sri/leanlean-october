import RequestProject.StrictThreeBoundarySquared
import RequestProject.Tac


/-! Actual chains in strict lower intervals and their cone fillings. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def strictLowerIncl (c : P) : Hom (strictOrderCx (Set.Iio c)) (strictOrderCx P) :=
  strictOrderCxMap Subtype.val (by tauto)
