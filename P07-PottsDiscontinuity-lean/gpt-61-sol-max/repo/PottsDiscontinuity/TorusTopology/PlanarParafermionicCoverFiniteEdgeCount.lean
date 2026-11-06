/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverGraph

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

def parafermionicCoverForward (u v : ParafermionicCoverVertex)  :=
   u.1.1 + 1 = v.1.1 ∧ u.1.2 = v.1.2  ∨
   u.1.1 = v.1.1 ∧ u.1.2 + 1 = v.1.2 

theorem parafermionicCover_adj_forward_or_reverse {u v : ParafermionicCoverVertex}
    (h : parafermionicCoverGraph.Adj u v) :
    parafermionicCoverForward u v ∨ parafermionicCoverForward v u := by
  rcases u with ⟨⟨x,y⟩,k⟩
  
  
  dsimp [parafermionicCoverForward] at *
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem parafermionicCoverForward_not_reverse {u v : ParafermionicCoverVertex}
    (h₁ : parafermionicCoverForward u v) (h₂ : parafermionicCoverForward v u) : False := by
  grind +locals

def coverHorizontalBase (n : ℕ) : Finset LatticeVertex :=
  Finset.Ico (-(n:ℤ)) n ×ˢ Finset.Icc (-(n:ℤ)) n

def coverVerticalBase (n : ℕ) : Finset LatticeVertex :=
  Finset.Icc (-(n:ℤ)) n ×ˢ Finset.Ico (-(n:ℤ)) n

def coverSheets (n : ℕ) : Finset ℤ :=
  Finset.Icc (-((n^5:ℕ):ℤ)) ((n^5:ℕ):ℤ)

def coverHorizontalBad (n : ℕ) : Finset (LatticeVertex × ℤ) :=
  (({0} : Finset ℤ) ×ˢ Finset.Ico (-(n:ℤ)) 0) ×ˢ ({((n^5:ℕ):ℤ)} : Finset ℤ)

def coverHorizontalIndex (n : ℕ)  :=
   coverHorizontalBase n ×ˢ coverSheets n  \ coverHorizontalBad n

def coverVerticalIndex (n : ℕ)  :=
  coverVerticalBase n ×ˢ coverSheets n

section

variable (n : ℕ)


private theorem cover_Ico_card  :
    (Finset.Ico (-(n:ℤ)) n).card = 2*n := by
  simp_all <;> omega

private theorem cover_Icc_card  :
    (Finset.Icc (-(n:ℤ)) n).card = 2*n+1 := by
  simp_all <;> omega

private theorem coverHorizontalBase_card  :
    (coverHorizontalBase n).card = 2*n*(2*n+1) := by
  unfold coverHorizontalBase
  rw [Finset.card_product, cover_Ico_card, cover_Icc_card]

private theorem coverVerticalBase_card  :
    (coverVerticalBase n).card = (2*n+1)*2*n := by
  unfold coverVerticalBase
  rw [Finset.card_product, cover_Icc_card, cover_Ico_card]
  ring

private theorem coverSheets_card  :
    (coverSheets n).card = 2*n^5+1 := by
  unfold coverSheets
  apply Nat.cast_injective (R := ℤ)
  rw [Int.card_Icc_of_le (a := - (n^5:ℕ) ) (b :=  (n^5:ℕ) ) (by omega)]
  push_cast
  ring

private theorem coverHorizontalBad_card  :
    (coverHorizontalBad n).card = n := by
  simp [coverHorizontalBad]

private theorem coverHorizontalBad_subset  :
    coverHorizontalBad n ⊆ coverHorizontalBase n ×ˢ coverSheets n := by
  grind +locals

private theorem coverHorizontalIndex_card  :
    (coverHorizontalIndex n).card = 2*n*(2*n+1)*(2*n^5+1)-n := by
  rw [coverHorizontalIndex, Finset.card_sdiff_of_subset (coverHorizontalBad_subset n),
    Finset.card_product, coverHorizontalBase_card, coverSheets_card,
    coverHorizontalBad_card]

private theorem coverVerticalIndex_card  :
    (coverVerticalIndex n).card = 2*n*(2*n+1)*(2*n^5+1) := by
  simp [coverVerticalIndex, Finset.card_product, coverVerticalBase_card, coverSheets_card]
  ring

end

noncomputable def coverForwardPairFinset (n : ℕ) : Finset
    (ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun p =>
    parafermionicCoverForward p.1.1 p.2.1 ∧ (parafermionicCoverBoxGraph n).Adj p.1 p.2

def coverPairEdge {n : ℕ}
    (p : ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n)  := s(p.1,p.2)

private theorem coverForwardPairFinset_image_eq_edgeFinset (n : ℕ) :
    (coverForwardPairFinset n).image coverPairEdge =
      (parafermionicCoverBoxGraph n).edgeFinset := by
  
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨p,hp,rfl⟩
    simp only [coverForwardPairFinset, Finset.mem_filter] at hp
    simpa [coverPairEdge, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hp.2.2
  · intro he
    have hAdj : e ∈ (parafermionicCoverBoxGraph n).edgeSet :=
      SimpleGraph.mem_edgeFinset.mp he
    let a := e.out.1
    let b := e.out.2
    have hout : s(a,b) = e := e.out_eq
    have hab : (parafermionicCoverBoxGraph n).Adj a b := by
      rw [← hout] at hAdj
      aesop
    
    rcases  parafermionicCover_adj_forward_or_reverse hab  with hf | hf
    · apply Finset.mem_image.mpr
      refine ⟨(a,b), ?_, ?_⟩
      · simp only [coverForwardPairFinset, Finset.mem_filter]
        exact ⟨by simp, ⟨hf, hab⟩⟩
      · exact hout
    · apply Finset.mem_image.mpr
      refine ⟨(b,a), ?_, ?_⟩
      · simp only [coverForwardPairFinset, Finset.mem_filter]
        exact ⟨by simp, ⟨hf, hab.symm⟩⟩
      · simpa [coverPairEdge, Sym2.eq_swap] using hout

private theorem coverForwardPairFinset_card_eq_edgeFinset_card (n : ℕ) :
    (coverForwardPairFinset n).card = (parafermionicCoverBoxGraph n).edgeFinset.card := by
  classical
  rw [← coverForwardPairFinset_image_eq_edgeFinset]
  symm
  apply Finset.card_image_of_injOn
  intro p hp q hq heq
  rcases p with ⟨p₁,p₂⟩
  
  
  
  rcases Sym2.eq_iff.mp heq with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · cases h1
    cases h2
    rfl
  · cases h1
    cases h2
    exact False.elim (parafermionicCoverForward_not_reverse  (Finset.mem_filter.mp hp).right.left   (Finset.mem_filter.mp hq).right.left )

def coverHorizontalRawPair (z : LatticeVertex × ℤ) :
    ParafermionicCoverVertex × ParafermionicCoverVertex :=
  ( (z.1, z.2) , parafermionicCoverNeighborLift  (z.1,z.2)  (z.1.1+1,z.1.2))

def coverVerticalRawPair (z : LatticeVertex × ℤ) :
    ParafermionicCoverVertex × ParafermionicCoverVertex :=
  ( (z.1, z.2) , parafermionicCoverNeighborLift  (z.1,z.2)  (z.1.1,z.1.2+1))

section

variable (n : ℕ) (z : LatticeVertex × ℤ)


private theorem coverHorizontalIndex_bounds 
    (hz : z ∈ coverHorizontalIndex n) :
    -(n:ℤ) ≤ z.1.1 ∧ z.1.1 < n ∧ -(n:ℤ) ≤ z.1.2 ∧ z.1.2 ≤ n ∧
      -((n^5:ℕ):ℤ) ≤ z.2 ∧ z.2 ≤ (n^5:ℕ) ∧
      ¬ (z.1.1=0 ∧ z.1.2<0 ∧ z.2=(n^5:ℕ)) := by
  grind +locals

private theorem coverVerticalIndex_bounds 
    (hz : z ∈ coverVerticalIndex n) :
    -(n:ℤ) ≤ z.1.1 ∧ z.1.1 ≤ n ∧ -(n:ℤ) ≤ z.1.2 ∧ z.1.2 < n ∧
      -((n^5:ℕ):ℤ) ≤ z.2 ∧ z.2 ≤ (n^5:ℕ) := by
  grind +locals

 theorem coverHorizontalRawPair_mem 
    (hz : z ∈ coverHorizontalIndex n) :
    (coverHorizontalRawPair z).1 ∈ parafermionicCoverBoxVertices n ∧
      (coverHorizontalRawPair z).2 ∈ parafermionicCoverBoxVertices n := by
  rcases coverHorizontalIndex_bounds n z hz with
    ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi,hbad⟩
  
  
  
  have hshift : parafermionicCoverSheetShift z.1 (z.1.1+1,z.1.2) =
      if z.1.1=0 ∧ z.1.2<0 then 1 else 0 := by
    grind [parafermionicCoverSheetShift]
  
  
  change  (z.1,z.2) ∈ parafermionicCoverBoxVertices n  ∧
     parafermionicCoverNeighborLift (z.1,z.2) (z.1.1+1,z.1.2) ∈
      parafermionicCoverBoxVertices n 
  constructor
  · rw [parafermionicCoverBoxVertices_mem]
    grind
  · rw [parafermionicCoverBoxVertices_mem]
    simp only [parafermionicCoverNeighborLift]
    grind

 theorem coverVerticalRawPair_mem 
    (hz : z ∈ coverVerticalIndex n) :
    (coverVerticalRawPair z).1 ∈ parafermionicCoverBoxVertices n ∧
      (coverVerticalRawPair z).2 ∈ parafermionicCoverBoxVertices n := by
  rcases coverVerticalIndex_bounds n z hz with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi⟩
  change  (z.1,z.2) ∈ parafermionicCoverBoxVertices n  ∧
     parafermionicCoverNeighborLift (z.1,z.2) (z.1.1,z.1.2+1) ∈
      parafermionicCoverBoxVertices n 
  constructor
  · rw [parafermionicCoverBoxVertices_mem]
    grind
  · rw [parafermionicCoverBoxVertices_mem]
    simp only [parafermionicCoverNeighborLift]
    have hshift : parafermionicCoverSheetShift z.1 (z.1.1,z.1.2+1)=0 := by
      unfold parafermionicCoverSheetShift
      simp
    grind

end

noncomputable def coverVerticalPairs (n : ℕ)  :=
  (coverForwardPairFinset n).filter fun p => p.1.1.1.2 + 1 = p.2.1.1.2

noncomputable def verticalIndexPair (n : ℕ) (z : LatticeVertex × ℤ)
    (hz : z ∈ coverVerticalIndex n) :
    ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n :=
  ⟨⟨(coverVerticalRawPair z).1, (coverVerticalRawPair_mem n z hz).1⟩,
   ⟨(coverVerticalRawPair z).2, (coverVerticalRawPair_mem n z hz).2⟩⟩

private theorem verticalIndexPair_mem (n : ℕ) (z : LatticeVertex × ℤ)
    (hz : z ∈ coverVerticalIndex n) : verticalIndexPair n z hz ∈
      coverVerticalPairs n := by
  unfold coverVerticalPairs
  rw [Finset.mem_filter]
  constructor
  · simp only [coverForwardPairFinset, Finset.mem_filter]
    
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_, ?_⟩
    · 
      exact Or.inr ⟨rfl, rfl⟩
    · change parafermionicCoverGraph.Adj (z.1,z.2)
        (parafermionicCoverNeighborLift (z.1,z.2) (z.1.1,z.1.2+1))
      apply parafermionicCoverNeighborLift_adj
      rw [squareLattice_adj_iff]
      simp_all
  · rfl

private theorem coverVerticalIndex_card_bij (n : ℕ) :
    (coverVerticalIndex n).card = (coverVerticalPairs n).card := by
  
  apply Finset.card_bij  (verticalIndexPair n) 
  · exact verticalIndexPair_mem n
  · simp_all [ParafermionicCoverBoxVertex, verticalIndexPair, coverVerticalRawPair]
  · intro p hp
    simp only [coverVerticalPairs, Finset.mem_filter] at hp
    rcases hp with ⟨hp,hy⟩
    have hparts : parafermionicCoverForward p.1.1 p.2.1 ∧
        (parafermionicCoverBoxGraph n).Adj p.1 p.2 := by
      simpa [coverForwardPairFinset] using hp
    have hbase : p.2.1.1.1 = p.1.1.1.1 ∧ p.2.1.1.2 = p.1.1.1.2+1 := by
      grind +locals
    
    have hsecond : p.2.1 = parafermionicCoverNeighborLift p.1.1
        (p.1.1.1.1,p.1.1.1.2+1) := by
      apply parafermionicCoverNeighborLift_unique
      all_goals aesop
    let z  := ((p.1.1.1.1,p.1.1.1.2),p.1.1.2)
    
    refine ⟨z, by
                 simp only [coverVerticalIndex, coverVerticalBase, coverSheets, Finset.mem_product,
                   Finset.mem_Icc, Finset.mem_Ico]
                 rcases (parafermionicCoverBoxVertices_mem n p.1.1).mp p.1.2 with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi⟩
                 rcases (parafermionicCoverBoxVertices_mem n p.2.1).mp p.2.2 with ⟨_,_,_,hyhi2,_,_⟩
                 grind ,?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [verticalIndexPair, coverVerticalRawPair, z, hsecond]

noncomputable def coverHorizontalPairs (n : ℕ)  :=
  (coverForwardPairFinset n).filter fun p => p.1.1.1.1 + 1 = p.2.1.1.1

noncomputable def horizontalIndexPair (n : ℕ) (z : LatticeVertex × ℤ)
    (hz : z ∈ coverHorizontalIndex n) :
    ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n :=
  ⟨⟨(coverHorizontalRawPair z).1, (coverHorizontalRawPair_mem n z hz).1⟩,
   ⟨(coverHorizontalRawPair z).2, (coverHorizontalRawPair_mem n z hz).2⟩⟩

section

variable (n : ℕ)


private theorem horizontalIndexPair_mem  (z : LatticeVertex × ℤ)
    (hz : z ∈ coverHorizontalIndex n) : horizontalIndexPair n z hz ∈
      coverHorizontalPairs n := by
  unfold coverHorizontalPairs
  rw [Finset.mem_filter]
  constructor
  · simp only [coverForwardPairFinset, Finset.mem_filter]
    
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_, ?_⟩
    · 
      exact Or.inl ⟨rfl,rfl⟩
    · change parafermionicCoverGraph.Adj (z.1,z.2)
        (parafermionicCoverNeighborLift (z.1,z.2) (z.1.1+1,z.1.2))
      apply parafermionicCoverNeighborLift_adj
      rw [squareLattice_adj_iff]
      simp_all
  · rfl

private theorem coverHorizontalIndex_card_bij  :
    (coverHorizontalIndex n).card = (coverHorizontalPairs n).card := by
  
  apply Finset.card_bij  (horizontalIndexPair n) 
  · exact horizontalIndexPair_mem n
  · simp_all [ParafermionicCoverBoxVertex, horizontalIndexPair, coverHorizontalRawPair]
  · intro p hp
    simp only [coverHorizontalPairs, Finset.mem_filter] at hp
    rcases hp with ⟨hp,hx⟩
    have hparts :
        parafermionicCoverForward p.1.1 p.2.1 ∧
        (parafermionicCoverBoxGraph n).Adj p.1 p.2 := by
      simpa [coverForwardPairFinset] using hp
    have hbase : p.2.1.1.1 = p.1.1.1.1+1 ∧ p.2.1.1.2 = p.1.1.1.2 := by
      grind +locals
    have hadj : parafermionicCoverGraph.Adj p.1.1 p.2.1 := hparts.2
    have hshift := parafermionicCover_sheetShift_of_adj hadj
    have hsecond : p.2.1 = parafermionicCoverNeighborLift p.1.1
        (p.1.1.1.1+1,p.1.1.1.2) := by
      apply parafermionicCoverNeighborLift_unique
      all_goals grind
    let z  := ((p.1.1.1.1,p.1.1.1.2),p.1.1.2)
    
    refine ⟨z,  by
                  simp only [coverHorizontalIndex, Finset.mem_sdiff, Finset.mem_product,
                    coverHorizontalBase, coverSheets, Finset.mem_Ico, Finset.mem_Icc,
                    coverHorizontalBad, Finset.mem_singleton]
                  rcases (parafermionicCoverBoxVertices_mem n p.1.1).mp p.1.2 with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi⟩
                  rcases (parafermionicCoverBoxVertices_mem n p.2.1).mp p.2.2 with ⟨_,hxhi2,_,_,_,hkhi2⟩
                  
                  refine ⟨?_,?_⟩
                  · grind
                  · grind [parafermionicCoverSheetShift] , ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [horizontalIndexPair, coverHorizontalRawPair, z, hsecond]

private theorem coverForwardPairFinset_eq_union  :
    coverForwardPairFinset n = coverHorizontalPairs n ∪ coverVerticalPairs n := by
  grind +locals

private theorem coverHorizontalVertical_disjoint  :
    Disjoint (coverHorizontalPairs n) (coverVerticalPairs n) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  simp only [coverHorizontalPairs, coverVerticalPairs, Finset.mem_filter] at hp hq
  rcases hp with ⟨hp,hx⟩
  
  have hforward : parafermionicCoverForward p.1.1 p.2.1 ∧
      (parafermionicCoverBoxGraph n).Adj p.1 p.2 := by
    simpa [coverForwardPairFinset] using hp
  rcases hforward.1 with hh | hv <;> omega

 theorem parafermionicCoverBoxGraph_edgeFinset_card_add_n  (hn : 0 < n) :
    (parafermionicCoverBoxGraph n).edgeFinset.card + n =
      4*n*(2*n+1)*(2*n^5+1) := by
  
  rw [←  coverForwardPairFinset_card_eq_edgeFinset_card n , coverForwardPairFinset_eq_union,
    Finset.card_union_of_disjoint (coverHorizontalVertical_disjoint n),
    ← coverHorizontalIndex_card_bij, ← coverVerticalIndex_card_bij,
    coverHorizontalIndex_card, coverVerticalIndex_card]
  grind

end

end PottsDiscontinuity.TorusTopology.Planar.Medial
