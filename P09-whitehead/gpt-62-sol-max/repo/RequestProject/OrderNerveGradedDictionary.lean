module

public import RequestProject.NerveCoordinates
public import RequestProject.MathlibOrderNerveChainBoundary

@[expose] public section

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
open scoped Simplicial
variable {P : Type} [PartialOrder P]

/-- An order-nerve simplex, with all its vertices retained in order. -/
def orderNerveVertexList {n : ℕ} (s : ComposableArrows P n) : List P :=
  List.ofFn s.obj

theorem orderNerveVertexList_chain {n : ℕ} (s : ComposableArrows P n) :
    List.IsChain (· ≤ ·) (orderNerveVertexList s) := by
  rw [orderNerveVertexList, List.isChain_iff_pairwise, List.pairwise_ofFn]
  intro i j hij
  exact s.monotone hij.le

theorem orderNerveVertexList_length {n : ℕ} (s : ComposableArrows P n) :
    (orderNerveVertexList s).length = n + 1 := List.length_ofFn

theorem orderNerveVertexList_injective (n : ℕ) :
    Function.Injective (orderNerveVertexList (P := P) (n := n)) := by
  intro s t h
  exact CategoryTheory.Functor.ext (congrFun (List.ofFn_injective h))

/-- Every increasing list of the required length is a genuine Mathlib simplex. -/
def orderNerveOfVertexList (n : ℕ) (l : List P)
    (hl : List.IsChain (· ≤ ·) l) (hlen : l.length = n + 1) :
    ComposableArrows P n :=
  (show Monotone (fun i  => l[i.val]'(by omega)) from by
      intro i j hij
      grind [List.pairwise_iff_getElem.mp]).functor

theorem orderNerveVertexList_ofVertexList (n : ℕ) (l : List P)
    (hl : List.IsChain (· ≤ ·) l) (hlen : l.length = n + 1) :
    orderNerveVertexList (orderNerveOfVertexList n l hl hlen) = l := by
  apply List.ext_getElem
  · simpa [orderNerveVertexList] using hlen.symm
  · intro i hi hj
    simp only [orderNerveVertexList, List.getElem_ofFn]
    rfl

/-- Coefficient-preserving encoding, in arbitrary degree. -/
noncomputable def orderNerveGradedEncode (n : ℕ) :
    (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun s => of (orderNerveVertexList s))

theorem orderNerveGradedEncode_single (n : ℕ) (s : ComposableArrows P n) (r : ℤ) :
    orderNerveGradedEncode n (Finsupp.single s r) = r • of (orderNerveVertexList s) :=
  Finsupp.linearCombination_single ℤ r s

def orderNerveVertexEmbedding (n : ℕ) : ComposableArrows P n ↪ List P :=
  ⟨orderNerveVertexList, orderNerveVertexList_injective n⟩

noncomputable def orderNerveGradedDecode (n : ℕ) :
    Nerve.Ch P →ₗ[ℤ] (ComposableArrows P n →₀ ℤ) := Nerve.decode (orderNerveVertexEmbedding n)

theorem orderNerveGradedDecode_of_vertexList (n : ℕ) (s : ComposableArrows P n) :
    orderNerveGradedDecode n (of (orderNerveVertexList s)) = Finsupp.single s 1 :=
  Nerve.decode_of (orderNerveVertexEmbedding n) s

theorem orderNerveGradedEncode_injective (n : ℕ) :
    Function.Injective (orderNerveGradedEncode (P := P) n) :=
  Nerve.encode_injective (orderNerveVertexEmbedding n)

theorem orderNerveGradedEncode_decode (n : ℕ) {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    orderNerveGradedEncode n (orderNerveGradedDecode n c) = Nerve.lengthProjection (n + 1) c :=
  Nerve.encode_decode (orderNerveVertexEmbedding n) _ orderNerveVertexList_length
    (fun l hl hn => ⟨orderNerveOfVertexList n l hl hn, orderNerveVertexList_ofVertexList n l hl hn⟩) hc

end FiniteChains.Comb
