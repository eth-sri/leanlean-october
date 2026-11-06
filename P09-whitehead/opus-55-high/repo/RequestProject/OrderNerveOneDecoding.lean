import RequestProject.OrderNerveOneDictionary
import RequestProject.Tac
noncomputable section


/-! Recovering genuine cellular one-cycles from homogeneous increasing nerve cycles. -/
bwd

namespace FiniteChains.Comb
open FreeAbelianGroup
universe u
variable {P : Type u} [PartialOrder P]

def decodeOrdVertexList : List P → P →₀ ℤ
  | [a] => Finsupp.single a 1
  | _ => 0

def decodeOrdNerve0 : Nerve.Ch P →+ (P →₀ ℤ) := lift decodeOrdVertexList

omit [PartialOrder P] in
theorem decodeOrdNerve0_encode (c : P →₀ ℤ) :
    decodeOrdNerve0 (ordNerveChain0 c) = c := by
  lin_ind c p n => simp [ordNerveChain0, decodeOrdNerve0, decodeOrdVertexList]

omit [PartialOrder P] in
theorem ordNerveChain0_injective : Function.Injective (ordNerveChain0 (P := P)) := by
  intro c d h
  simpa [decodeOrdNerve0_encode] using congrArg decodeOrdNerve0 h

theorem ordNerveChain1_cycle_iff c :
    Nerve.bdry (ordNerveChain1 c) = 0 ↔ bdry1 (orderCx P) c = 0 := by
  rw [← ordNerveChain0_bdry1]
  exact ⟨fun h => ordNerveChain0_injective (P := P) (by aesop),
    fun h => by simp_all⟩

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
        have h : a ≤ b := by simp_all
        simp [decodeOrdEdgeList, h, ordNerveChain1]
      | cons c l => rfl

theorem ordNerveChain1_decode (hc : c ∈ Nerve.Inc P) :
    ordNerveChain1 (decodeOrdNerve1 c) = Nerve.lengthProjection 2 c := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [decodeOrdNerve1_of]
    exact ordNerveChain1_decode_of hl
  | zero => simp
  | add x y _ _ hx hy => simp_all
  | neg x _ hx => simp_all
