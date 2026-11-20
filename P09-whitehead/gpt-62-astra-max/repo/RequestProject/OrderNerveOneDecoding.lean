module

public import RequestProject.OrderNerveOneDictionary

@[expose] public section

/-! Recovering genuine cellular one-cycles from homogeneous increasing nerve cycles. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open FreeAbelianGroup
universe u
variable {P : Type u} [PartialOrder P]

noncomputable def decodeOrdVertexList : List P → P →₀ ℤ
  | [a] => Finsupp.single a 1
  | _ => 0

noncomputable def decodeOrdNerve0 : Nerve.Ch P →+ (P →₀ ℤ) := lift decodeOrdVertexList

omit [PartialOrder P] in
theorem decodeOrdNerve0_encode (c : P →₀ ℤ) :
    decodeOrdNerve0 (ordNerveChain0 c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single p n => simp [ordNerveChain0, decodeOrdNerve0, decodeOrdVertexList]

omit [PartialOrder P] in
theorem ordNerveChain0_injective : Function.Injective (ordNerveChain0 (P := P)) := by
  intro c d h
  simpa only [decodeOrdNerve0_encode] using congrArg decodeOrdNerve0 h

theorem ordNerveChain1_cycle_iff (c : OrdEdge P →₀ ℤ) :
    Nerve.bdry (ordNerveChain1 c) = 0 ↔ bdry1 (orderCx P) c = 0 := by
  rw [← ordNerveChain0_bdry1]
  solve_by_elim [ordNerveChain0_injective]

theorem ordNerveChain1_decode_of {l : List P} (hl : List.IsChain (· ≤ ·) l) :
    ordNerveChain1 (decodeOrdEdgeList l) = Nerve.lengthProjection 2 (of l) := by
  classical
  cases l with
  | nil => rfl
  | cons a l =>
    cases l with
    | nil => rfl
    | cons b l =>
      cases l with
      | nil =>
        simp [decodeOrdEdgeList, (by simpa [List.isChain_cons] using hl), ordNerveChain1]
      | cons c l => rfl

theorem ordNerveChain1_decode {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    ordNerveChain1 (decodeOrdNerve1 c) = Nerve.lengthProjection 2 c := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    grind [decodeOrdNerve1_of, ordNerveChain1_decode_of]
  | zero => simp
  | add x y _ _ hx hy => simp_all
  | neg x _ hx => simp [map_neg, hx]

end FiniteChains.Comb
