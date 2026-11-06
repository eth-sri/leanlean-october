import Mathlib.Tactic

import RequestProject.NerveDegree
import RequestProject.MathlibOrderNerveChainBoundary

namespace FiniteChains.Nerve
open FreeAbelianGroup

/-- The recursive list boundary is the alternating face sum in every degree. -/
theorem bdryOn_ofFn {P : Type*} (n : ℕ) (v : Fin (n + 1) → P) :
    bdryOn (List.ofFn v) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
        of (List.ofFn (fun j : Fin n => v (i.succAbove j))) := by
  induction n with
  | zero => simp [List.ofFn_succ, bdryOn]
  | succ n ih =>
    rw [List.ofFn_succ, bdryOn_cons, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
      map_sum, map_zsmul, Fin.val_succ, pow_succ, mul_neg, mul_one]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [neg_smul]
    congr 1
    rw [consMap_of, List.ofFn_succ]
    simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]

end FiniteChains.Nerve

namespace FiniteChains.Comb
open CategoryTheory FreeAbelianGroup

variable {P : Type} [PartialOrder P]

  {n : ℕ}
/-- An order-nerve simplex, with all its vertices retained in order. -/
def orderNerveVertexList  (s : ComposableArrows P n)  :=
  List.ofFn s.obj

theorem orderNerveVertexList_chain  (s : ComposableArrows P n) :
    List.IsChain (· ≤ ·) (orderNerveVertexList s) := by
  rw [orderNerveVertexList, List.isChain_iff_pairwise, List.pairwise_ofFn]
  intro i j hij
  exact s.monotone hij.le

theorem orderNerveVertexList_length  (s : ComposableArrows P n) :
    (orderNerveVertexList s).length = n + 1 := List.length_ofFn

variable (n : ℕ)
theorem orderNerveVertexList_injective  :
    Function.Injective (orderNerveVertexList (P := P) (n := n)) := by
  intro s t h
  exact CategoryTheory.Functor.ext (fun i => congrFun (List.ofFn_injective h) i)

variable (l : List P)
/-- Every increasing list of the required length is a genuine Mathlib simplex. -/
def orderNerveOfVertexList  
    (hl : List.IsChain (· ≤ ·) l) (hlen : l.length = n + 1)  :=
  (show Monotone (fun i : Fin (n + 1) => l[i.val]'(by omega)) from by
      intro i j hij
      rcases hij.eq_or_lt with he | he
      · simp_all
      · exact (List.pairwise_iff_getElem.mp (List.isChain_iff_pairwise.mp hl))
          i.val j.val (by omega) (by omega) he).functor

theorem orderNerveVertexList_ofVertexList  
    (hl : List.IsChain (· ≤ ·) l) (hlen : l.length = n + 1) :
    orderNerveVertexList (orderNerveOfVertexList n l hl hlen) = l := by
  apply List.ext_getElem
  · classical simp_all [orderNerveVertexList]
  · classical solve_by_elim (transparency := .default) [List.getElem_ofFn]

/-- Coefficient-preserving encoding, in arbitrary degree. -/
noncomputable def orderNerveGradedEncode  :
    (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun s => of (orderNerveVertexList s))

theorem orderNerveGradedEncode_single  (s : ComposableArrows P n) (r : ℤ) :
    orderNerveGradedEncode n (Finsupp.single s r) = r • of (orderNerveVertexList s) :=
  Finsupp.linearCombination_single ℤ r s

noncomputable def orderNerveGradedDecodeList   :
    ComposableArrows P n →₀ ℤ := by
  classical
  exact if h : ∃ s : ComposableArrows P n, orderNerveVertexList s = l
    then Finsupp.single h.choose 1 else 0

noncomputable def orderNerveGradedDecode  :
    Nerve.Ch P →ₗ[ℤ] (ComposableArrows P n →₀ ℤ) :=
  (lift (orderNerveGradedDecodeList n)).toIntLinearMap

theorem orderNerveGradedDecode_of   :
    orderNerveGradedDecode n (of l) = orderNerveGradedDecodeList n l :=
  lift_apply_of _ _

theorem orderNerveGradedDecodeList_vertexList  (s : ComposableArrows P n) :
    orderNerveGradedDecodeList n (orderNerveVertexList s) = Finsupp.single s 1 := by
  classical
  have h : ∃ t : ComposableArrows P n, orderNerveVertexList t = orderNerveVertexList s := ⟨s, rfl⟩
  grind [orderNerveGradedDecodeList, orderNerveVertexList_injective]

theorem orderNerveGradedDecode_encode  (c : ComposableArrows P n →₀ ℤ) :
    orderNerveGradedDecode n (orderNerveGradedEncode n c) = c := by
  induction c using Finsupp.induction_linear <;> simp_all [orderNerveGradedEncode_single, orderNerveGradedDecode_of, orderNerveGradedDecodeList_vertexList]

theorem orderNerveGradedEncode_injective  :
    Function.Injective (orderNerveGradedEncode (P := P) n) := by
  intro c d h
  simpa [orderNerveGradedDecode_encode] using congrArg (orderNerveGradedDecode n) h

theorem orderNerveGradedEncode_decode  {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    orderNerveGradedEncode n (orderNerveGradedDecode n c) = Nerve.lengthProjection (n + 1) c := by
  classical
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [orderNerveGradedDecode_of, Nerve.lengthProjection_of]
    by_cases hlen : l.length = n + 1
    · have he := orderNerveVertexList_ofVertexList n l hl hlen
      rw [if_pos hlen, ← he, orderNerveGradedDecodeList_vertexList,
        orderNerveGradedEncode_single, one_smul]
    · aesop (add simp [orderNerveVertexList, orderNerveGradedDecodeList])
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | neg x _ hx => simp only [map_neg, hx]

end FiniteChains.Comb
