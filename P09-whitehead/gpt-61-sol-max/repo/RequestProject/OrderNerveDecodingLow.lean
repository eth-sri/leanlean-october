import Mathlib.Tactic

import RequestProject.OrderNerveOneDecoding

namespace FiniteChains.Comb
open FreeAbelianGroup
variable {P : Type u}

@[simp] theorem decodeOrdNerve0_of (l : List P) :
    decodeOrdNerve0 (of l) = decodeOrdVertexList l := lift_apply_of _ _

theorem ordNerveChain0_decode (c : Nerve.Ch P) :
    ordNerveChain0 (decodeOrdNerve0 c) = Nerve.lengthProjection 1 c := by
  classical
  apply Nerve.ext_apply
    (F := ordNerveChain0.toAddMonoidHom.comp decodeOrdNerve0) (G := Nerve.lengthProjection 1)
  intro l
  cases l with
  | nil => simp [decodeOrdVertexList]
  | cons a l =>
    cases l <;> simp_all [decodeOrdVertexList, ordNerveChain0]

end FiniteChains.Comb
