module
public import Mathlib.Tactic

public import Erdos821.P4Bridge.Sites
public import Erdos821.P4Bridge.Support

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.P4Bridge
open Blueprint.Graph P4Probe
noncomputable section
variable {P : PrimeGroups} {J ell m : ℕ}

def sharedRows (ν : Pattern P J ell m) (g : P.BigGroup) : Finset (Fin J) :=
  Finset.univ \ ν.changed g.val

abbrev SharedRows (ν : Pattern P J ell m) := BigRowPartial (sharedRows ν)
abbrev SideRows (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (side : Bool) :=
  BigRowPartial (patternAuxCoordinates ν block side)

lemma mem_sideRows (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
     side  (g : P.BigGroup) (i : Fin J) :
    i ∈ patternAuxCoordinates ν block side g ↔ block g = side ∧ i ∈ ν.changed g.val := by
  grind [patternAuxCoordinates]

def rowJoin (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideRows ν block false) (b : SideRows ν block true) :
    P.BigLabels J := fun g i =>
  if hi : i ∈ ν.changed g.val then
    if hb : block g = false then a g ⟨i, (mem_sideRows ν block false g i).mpr ⟨hb, hi⟩⟩
    else b g ⟨i, (mem_sideRows ν block true g i).mpr ⟨by cases h : block g <;> simp_all, hi⟩⟩
  else s g ⟨i, by simp [sharedRows, hi]⟩

section
variable (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (s : SharedRows ν) (a : SideRows ν block false) (b : SideRows ν block true) (g : P.BigGroup)


@[simp] lemma rowJoin_shared    
         
      (i : {i // i ∈ sharedRows ν g}) :
    rowJoin ν block s a b g i.val = s g i := by
  grind [sharedRows, rowJoin]

@[simp] lemma rowJoin_false    
         
      (i : {i // i ∈ patternAuxCoordinates ν block false g}) :
    rowJoin ν block s a b g i.val = a g i := by
  grind [mem_sideRows, rowJoin]

@[simp] lemma rowJoin_true    
         
      (i : {i // i ∈ patternAuxCoordinates ν block true g}) :
    rowJoin ν block s a b g i.val = b g i := by
  grind [mem_sideRows, rowJoin]

end

def rowSplit (ν : Pattern P J ell m) (block : P.BigGroup → Bool) :
    P.BigLabels J ≃ SharedRows ν × SideRows ν block false × SideRows ν block true where
  toFun u := (fun g i => u g i.val, (fun g i => u g i.val), fun g i => u g i.val)
  invFun z := rowJoin ν block z.1 z.2.1 z.2.2
  left_inv u := by
    grind [rowJoin]
  right_inv z := by
    simp_all

def rowWeight (S : P.BigGroup → Finset (Fin J)) (x : BigRowPartial S) : ℝ :=
  ∏ g, ∏ i, P.mu g.val (x g i)

def rowProduct (S : P.BigGroup → Finset (Fin J)) (x : BigRowPartial S) : ℕ :=
  ∏ g, ∏ i, (x g i).val

section
variable (hV : ∀ g, 0 < P.V g) (S : P.BigGroup → Finset (Fin J)) (x : BigRowPartial S)


include hV in
lemma rowWeight_sum     :
    ∑ x : BigRowPartial S, rowWeight S x = 1 := by
  unfold rowWeight
  trans ∏ g : P.BigGroup, ∑ x : {i // i ∈ S g} → P.Prime g.val,
    ∏ i, P.mu g.val (x i)
  · exact (Fintype.prod_sum (fun (g : P.BigGroup)
      (x : {i // i ∈ S g} → P.Prime g.val) => ∏ i, P.mu g.val (x i))).symm
  apply Finset.prod_eq_one
  intro g _
  trans ∏ _i : {i // i ∈ S g}, ∑ x : P.Prime g.val, P.mu g.val x
  · exact (Fintype.prod_sum (fun (_i : {i // i ∈ S g}) (x : P.Prime g.val) =>
      P.mu g.val x)).symm
  · simp only [graph_mu_sum P g.val (hV g.val), Finset.prod_const_one]

include hV in
lemma rowWeight_pos    
      : 0 < rowWeight S x := by
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  exact graph_mu_pos P g.val (hV g.val) _

lemma rowProduct_pos     :
    0 < rowProduct S x := by
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  exact (P.prime g.val _ (x g i).property).pos

end

lemma row_split_product {R : Type*} [CommMonoid R] (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (v : P.BigGroup → Fin J → R) :
    (∏ g, ∏ i, v g i) =
      (∏ g, ∏ i : {i // i ∈ sharedRows ν g}, v g i.val) *
      (∏ g, ∏ i : {i // i ∈ patternAuxCoordinates ν block false g}, v g i.val) *
      (∏ g, ∏ i : {i // i ∈ patternAuxCoordinates ν block true g}, v g i.val) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  simp only [Finset.prod_coe_sort]
  unfold sharedRows patternAuxCoordinates
  cases hb : block g <;> simp only [ite_true, Bool.false_eq_true,
    Bool.true_eq_false, ite_false, Finset.prod_empty, mul_one]
  all_goals
    rw [← Finset.prod_union (Finset.sdiff_disjoint), Finset.sdiff_union_of_subset (Finset.subset_univ _)]

def sideCounts (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (side : Bool) :=
  selectedCounts (patternAuxCoordinates ν block side)
abbrev SideTuple (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (side : Bool) :=
  Blueprint.Analytic.Tuple (analyticGroups P) (sideCounts ν block side)

instance analyticTupleFintype (P : PrimeGroups) (k : P.Group → ℕ) :
    Fintype (Blueprint.Analytic.Tuple (analyticGroups P) k) :=
  inferInstanceAs (Fintype (∀ g : P.Group, Fin (k g) → P.Prime g))

def prefixSplit (ν : Pattern P J ell m) (block : P.BigGroup → Bool) :
    P.BigLabels J ≃ SharedRows ν × SideTuple ν block false × SideTuple ν block true :=
  (rowSplit ν block).trans (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (rowPartialTupleEquiv _) (rowPartialTupleEquiv _)))

def labelSplit (ν : Pattern P J ell m) (block : P.BigGroup → Bool) :
    P.BigLabels (J + ell) ≃
      (SharedRows ν × SideTuple ν block false × SideTuple ν block true) × P.BigLabels ell :=
  (splitBigLabels P J ell).trans (Equiv.prodCongr (prefixSplit ν block) (Equiv.refl _))

def labelJoin (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) : P.BigLabels (J + ell) :=
  (labelSplit ν block).symm ((s, a, b), t)

section
variable (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (u : P.BigLabels J)


lemma idealMass_rowSplit    
      :
    P.idealMass u = rowWeight (sharedRows ν) ((rowSplit ν block u).1) *
      rowWeight (patternAuxCoordinates ν block false) ((rowSplit ν block u).2.1) *
      rowWeight (patternAuxCoordinates ν block true) ((rowSplit ν block u).2.2) :=
  row_split_product ν block (fun g i => P.mu g.val (u g i))

lemma idealMass_prefixSplit    
      :
    P.idealMass u = rowWeight (sharedRows ν) ((prefixSplit ν block u).1) *
      Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false)
        ((prefixSplit ν block u).2.1) *
      Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true)
        ((prefixSplit ν block u).2.2) := by
  rw [idealMass_rowSplit ν block u]
  change _ = rowWeight (sharedRows ν) ((rowSplit ν block u).1) *
    Blueprint.Analytic.tupleWeight (analyticGroups P) _
      (rowPartialTuple _ ((rowSplit ν block u).2.1)) *
    Blueprint.Analytic.tupleWeight (analyticGroups P) _
      (rowPartialTuple _ ((rowSplit ν block u).2.2))
  rw [rowPartialTuple_weight, rowPartialTuple_weight]
  rfl

lemma idealMass_labelJoin    
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) :
    P.idealMass (labelJoin ν block s a b t) = rowWeight (sharedRows ν) s *
      Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false) a *
      Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true) b * P.idealMass t := by
  rw [idealMass_split, idealMass_prefixSplit ν block]
  simp_all [labelSplit, prefixSplit, splitBigLabels, labelJoin, Prod.fst, Prod.snd]

end

end
end Erdos821.P4Bridge
