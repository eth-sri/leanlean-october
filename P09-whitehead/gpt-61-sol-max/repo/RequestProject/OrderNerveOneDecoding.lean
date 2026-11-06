import Mathlib.Tactic

import RequestProject.OrderNerveOneDictionary

/-! Recovering genuine cellular one-cycles from homogeneous increasing nerve cycles. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open FreeAbelianGroup
variable {P : Type u} [PartialOrder P]

noncomputable def decodeOrdVertexList : List P → P →₀ ℤ
  | [a] => Finsupp.single a 1
  | _ => 0

noncomputable def decodeOrdNerve0 : Nerve.Ch P →+ (P →₀ ℤ) := lift decodeOrdVertexList

section
omit [PartialOrder P]
theorem decodeOrdNerve0_encode (c : P →₀ ℤ) :
    decodeOrdNerve0 (ordNerveChain0 c) = c := by
  induction c using Finsupp.induction_linear <;> simp_all [ordNerveChain0, decodeOrdNerve0, decodeOrdVertexList]

theorem ordNerveChain0_injective : Function.Injective (ordNerveChain0 (P := P)) := by
  intro c d h
  simpa [decodeOrdNerve0_encode] using congrArg decodeOrdNerve0 h
end

theorem ordNerveChain1_cycle_iff (c : OrdEdge P →₀ ℤ) :
    Nerve.bdry (ordNerveChain1 c) = 0 ↔ bdry1 (orderCx P) c = 0 := by
  rw [← ordNerveChain0_bdry1]
  exact ⟨fun h => ordNerveChain0_injective (P := P) (h.trans (map_zero _).symm),
    fun h => by rw [h, map_zero]⟩

theorem ordNerveChain1_decode_of {l : List P} (hl : List.IsChain (· ≤ ·) l) :
    ordNerveChain1 (decodeOrdEdgeList l) = Nerve.lengthProjection 2 (of l) := by
  classical
  cases l with
  | nil => simp [decodeOrdEdgeList]
  | cons a l =>
    cases l <;> aesop (add simp [decodeOrdEdgeList, ordNerveChain1])

theorem ordNerveChain1_decode {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    ordNerveChain1 (decodeOrdNerve1 c) = Nerve.lengthProjection 2 c := by
  classical
  induction hc using AddSubgroup.closure_induction <;> aesop (add simp [ordNerveChain1_decode_of])

end FiniteChains.Comb
