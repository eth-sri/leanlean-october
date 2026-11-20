module

public import RequestProject.NerveDegree
public import RequestProject.MathlibOrderNerveChainBoundary

@[expose] public section

noncomputable section

namespace FiniteChains.Nerve
open FreeAbelianGroup

/-- The recursive list boundary is the alternating face sum in every degree. -/
theorem bdryOn_ofFn {P : Type*} (n : ℕ) (v : Fin _ → P) :
    bdryOn (List.ofFn v) =
      ∑ i : Fin _, (-1) ^ i.val •
        of (List.ofFn (fun j : Fin n => v (i.succAbove j))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, bdryOn_cons, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
      map_sum, map_zsmul, Fin.val_succ, pow_succ, mul_neg, mul_one]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    simp

end FiniteChains.Nerve

namespace FiniteChains.Comb
open CategoryTheory FreeAbelianGroup
open scoped Simplicial
variable {P : Type} [PartialOrder P]

section

variable {n : ℕ} (s : ComposableArrows P n)
include n

/-- An order-nerve simplex, with all its vertices retained in order. -/
def orderNerveVertexList :=
  List.ofFn s.obj

theorem orderNerveVertexList_chain :
    List.IsChain (· ≤ ·) (orderNerveVertexList s) := by
  rw [orderNerveVertexList, List.isChain_iff_pairwise, List.pairwise_ofFn]
  intro i j hij
  exact s.monotone hij.le

theorem orderNerveVertexList_length :
    (orderNerveVertexList s).length = n + 1 := List.length_ofFn

end

variable (n : ℕ)

theorem orderNerveVertexList_injective :
    Function.Injective (orderNerveVertexList (P := P) (n := n)) := by
  intro s t h
  exact CategoryTheory.Functor.ext (fun i => congrFun (List.ofFn_injective h) i)

variable (l : List P) (hl : List.IsChain (· ≤ ·) l) (hlen : l.length = n + 1)

/-- Every increasing list of the required length is a genuine Mathlib simplex. -/
def orderNerveOfVertexList :=
  (show Monotone (fun i : Fin (n + 1) => l[i.val]'(by omega)) from by
      intro i j hij
      rcases hij.eq_or_lt with he | he
      · simp_all
      · exact (List.pairwise_iff_getElem.mp (List.isChain_iff_pairwise.mp hl))
          i.val j.val _ _ he).functor

theorem orderNerveVertexList_ofVertexList :
    orderNerveVertexList (orderNerveOfVertexList n l hl hlen) = l := by
  apply List.ext_getElem
  · simp_all [orderNerveVertexList]
  · intro i hi hj
    simp only [orderNerveVertexList, List.getElem_ofFn]
    rfl

/-- Coefficient-preserving encoding, in arbitrary degree. -/
def orderNerveGradedEncode :
    (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun s => of (orderNerveVertexList s))

theorem orderNerveGradedEncode_single (s : ComposableArrows P n) (r : ℤ) :
    orderNerveGradedEncode n (Finsupp.single s r) = r • of (orderNerveVertexList s) :=
  by apply Finsupp.linearCombination_single

def orderNerveGradedDecodeList (l : List P) :
    ComposableArrows P n →₀ ℤ := by
  classical
  exact if h : ∃ s : ComposableArrows P n, orderNerveVertexList s = l
    then Finsupp.single h.choose 1 else 0

def orderNerveGradedDecode :
    Nerve.Ch P →ₗ[ℤ] (ComposableArrows P n →₀ ℤ) :=
  (lift (orderNerveGradedDecodeList n)).toIntLinearMap

theorem orderNerveGradedDecode_of (l : List P) :
    orderNerveGradedDecode n (of l) = orderNerveGradedDecodeList n l :=
  lift_apply_of _ _

theorem orderNerveGradedDecodeList_vertexList (s : ComposableArrows P n) :
    orderNerveGradedDecodeList n (orderNerveVertexList s) = Finsupp.single s 1 := by
  classical
  have h : ∃ t : ComposableArrows P n, orderNerveVertexList t = orderNerveVertexList s := ⟨s, rfl⟩
  rw [orderNerveGradedDecodeList, dif_pos h]
  rw [orderNerveVertexList_injective n h.choose_spec]

theorem orderNerveGradedDecode_encode (c : ComposableArrows P n →₀ ℤ) :
    orderNerveGradedDecode n (orderNerveGradedEncode n c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single s r =>
    simp [orderNerveGradedEncode_single, map_smul, orderNerveGradedDecode_of, orderNerveGradedDecodeList_vertexList]

theorem orderNerveGradedEncode_injective :
    Function.Injective (orderNerveGradedEncode (P := P) n) := by
  intro c d h
  simpa only [orderNerveGradedDecode_encode] using congrArg (orderNerveGradedDecode n) h

theorem orderNerveGradedEncode_decode {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    orderNerveGradedEncode n (orderNerveGradedDecode n c) = Nerve.lengthProjection (n + 1) c := by
  classical
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [orderNerveGradedDecode_of, Nerve.lengthProjection_of]
    by_cases hlen : l.length = n + 1
    · rw [if_pos hlen, ← (orderNerveVertexList_ofVertexList n l hl hlen), orderNerveGradedDecodeList_vertexList,
        orderNerveGradedEncode_single, one_smul]
    · have he : ¬ ∃ s : ComposableArrows P n, orderNerveVertexList s = l := by
        rintro ⟨s, rfl⟩
        solve_by_elim [orderNerveVertexList_length]
      rw [if_neg hlen, orderNerveGradedDecodeList, dif_neg he, map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp_all
  | neg x _ hx => simp [map_neg, hx]

end FiniteChains.Comb
