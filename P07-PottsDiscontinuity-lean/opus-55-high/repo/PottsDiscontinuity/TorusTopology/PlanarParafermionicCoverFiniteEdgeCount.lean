/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverGraph

public noncomputable section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

def parafermionicCoverForward (u v : ParafermionicCoverVertex) : Prop :=
  (u.1.1 + 1 = v.1.1 ∧ u.1.2 = v.1.2) ∨
  (u.1.1 = v.1.1 ∧ u.1.2 + 1 = v.1.2)

section
variable {u v : ParafermionicCoverVertex}
theorem parafermionicCover_adj_forward_or_reverse (h : parafermionicCoverGraph.Adj u v) :
    parafermionicCoverForward u v ∨ parafermionicCoverForward v u := by
  rcases u with ⟨⟨x,y⟩,k⟩
  dsimp [parafermionicCoverForward] at *
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem parafermionicCoverForward_not_reverse (h₁ : parafermionicCoverForward u v) (h₂ : parafermionicCoverForward v u) : False := by
  rcases h₁ with ⟨hx,hy⟩ | ⟨hx,hy⟩ <;>
    rcases h₂ with ⟨hx',hy'⟩ | ⟨hx',hy'⟩ <;> omega
end

section
variable (n : ℕ)
def coverHorizontalBase  : Finset LatticeVertex :=
  Finset.Ico (-(n:ℤ)) n ×ˢ Finset.Icc (-(n:ℤ)) n

def coverVerticalBase  : Finset LatticeVertex :=
  Finset.Icc (-(n:ℤ)) n ×ˢ Finset.Ico (-(n:ℤ)) n

def coverSheets  : Finset ℤ :=
  Finset.Icc (-((n^5:ℕ):ℤ)) ((n^5:ℕ):ℤ)

def coverHorizontalBad  : Finset (LatticeVertex × ℤ) :=
  (({0} : Finset ℤ) ×ˢ Finset.Ico (-(n:ℤ)) 0) ×ˢ ({((n^5:ℕ):ℤ)} : Finset ℤ)

def coverHorizontalIndex  : Finset (LatticeVertex × ℤ) :=
  (coverHorizontalBase n ×ˢ coverSheets n) \ coverHorizontalBad n

def coverVerticalIndex  : Finset (LatticeVertex × ℤ) :=
  coverVerticalBase n ×ˢ coverSheets n

theorem cover_Ico_card  :
    (Finset.Ico (-(n:ℤ)) n).card = 2*n := by
  simp
  omega

theorem cover_Icc_card  :
    (Finset.Icc (-(n:ℤ)) n).card = 2*n+1 := by
  simp
  omega

theorem coverHorizontalBase_card  :
    (coverHorizontalBase n).card = 2*n*(2*n+1) := by
  unfold coverHorizontalBase
  rw [Finset.card_product, cover_Ico_card, cover_Icc_card]

theorem coverVerticalBase_card  :
    (coverVerticalBase n).card = (2*n+1)*2*n := by
  unfold coverVerticalBase
  rw [Finset.card_product, cover_Icc_card, cover_Ico_card]
  ring

theorem coverSheets_card  :
    (coverSheets n).card = 2*n^5+1 := by
  unfold coverSheets
  apply Nat.cast_injective (R := ℤ)
  rw [Int.card_Icc_of_le (a := -((n^5:ℕ):ℤ)) (b := ((n^5:ℕ):ℤ)) (by omega)]
  omega

theorem coverHorizontalBad_card  :
    (coverHorizontalBad n).card = n := by
  simp [coverHorizontalBad]

theorem coverHorizontalBad_subset  :
    coverHorizontalBad n ⊆ coverHorizontalBase n ×ˢ coverSheets n := by
  grind [coverHorizontalBad, coverHorizontalBase, coverSheets]

theorem coverHorizontalIndex_card  :
    (coverHorizontalIndex n).card = 2*n*(2*n+1)*(2*n^5+1)-n := by
  rw [coverHorizontalIndex, Finset.card_sdiff_of_subset (coverHorizontalBad_subset n),
    Finset.card_product, coverHorizontalBase_card, coverSheets_card,
    coverHorizontalBad_card]

theorem coverVerticalIndex_card  :
    (coverVerticalIndex n).card = 2*n*(2*n+1)*(2*n^5+1) := by
  simp [coverVerticalIndex, Finset.card_product, coverVerticalBase_card, coverSheets_card]
  ring

def coverForwardPairFinset  : Finset
    (ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun p =>
    parafermionicCoverForward p.1.1 p.2.1 ∧ (parafermionicCoverBoxGraph n).Adj p.1 p.2
end

def coverPairEdge {n : ℕ}
    (p : ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n) :
    Sym2 (ParafermionicCoverBoxVertex n) := s(p.1,p.2)

section
variable (n : ℕ)
theorem coverForwardPairFinset_image_eq_edgeFinset  :
    (coverForwardPairFinset n).image coverPairEdge =
      (parafermionicCoverBoxGraph n).edgeFinset := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨p,hp,rfl⟩
    simp only [coverForwardPairFinset, Finset.mem_filter] at hp
    simpa [coverPairEdge, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hp.2.2
  · intro he
    have hAdj :=
      SimpleGraph.mem_edgeFinset.mp he
    let a := e.out.1
    let b := e.out.2
    have hout : s(a,b) = e := e.out_eq
    have hab : (parafermionicCoverBoxGraph n).Adj a b := by
      rw [← hout] at hAdj
      aesop
    have hbase := parafermionicCover_adj_forward_or_reverse hab
    rcases hbase with hf | hf
    · apply Finset.mem_image.mpr
      refine ⟨(a,b), ?_, ?_⟩
      · simp only [coverForwardPairFinset, Finset.mem_filter]
        exact ⟨by simp, ⟨hf, hab⟩⟩
      aesop
    · apply Finset.mem_image.mpr
      refine ⟨(b,a), ?_, ?_⟩
      · simp only [coverForwardPairFinset, Finset.mem_filter]
        exact ⟨by simp, ⟨hf, hab.symm⟩⟩
      · simpa [coverPairEdge, Sym2.eq_swap] using hout

theorem coverForwardPairFinset_card_eq_edgeFinset_card  :
    (coverForwardPairFinset n).card = (parafermionicCoverBoxGraph n).edgeFinset.card := by
  rw [← coverForwardPairFinset_image_eq_edgeFinset]
  symm
  apply Finset.card_image_of_injOn
  intro p hp q hq heq
  rcases p with ⟨p₁,p₂⟩
  rcases q with ⟨q₁,q₂⟩
  have hpF : parafermionicCoverForward p₁.1 p₂.1 := by
    grind [coverForwardPairFinset]
  have hqF : parafermionicCoverForward q₁.1 q₂.1 := by
    grind [coverForwardPairFinset]
  rcases Sym2.eq_iff.mp heq with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · simp_all
  · grind [False.elim, parafermionicCoverForward_not_reverse]
end

def coverHorizontalRawPair (z : LatticeVertex × ℤ) :
    ParafermionicCoverVertex × ParafermionicCoverVertex :=
  (((z.1, z.2)), parafermionicCoverNeighborLift ((z.1,z.2)) (z.1.1+1,z.1.2))

def coverVerticalRawPair (z : LatticeVertex × ℤ) :
    ParafermionicCoverVertex × ParafermionicCoverVertex :=
  (((z.1, z.2)), parafermionicCoverNeighborLift ((z.1,z.2)) (z.1.1,z.1.2+1))

section
variable (n : ℕ) (z : LatticeVertex × ℤ)
theorem coverHorizontalIndex_bounds (hz : z ∈ coverHorizontalIndex n) :
    -(n:ℤ) ≤ z.1.1 ∧ z.1.1 < n ∧ -(n:ℤ) ≤ z.1.2 ∧ z.1.2 ≤ n ∧
      -((n^5:ℕ):ℤ) ≤ z.2 ∧ z.2 ≤ (n^5:ℕ) ∧
      ¬ (z.1.1=0 ∧ z.1.2<0 ∧ z.2=(n^5:ℕ)) := by
  grind [coverHorizontalIndex, coverHorizontalBase, coverSheets, coverHorizontalBad]

theorem coverVerticalIndex_bounds (hz : z ∈ coverVerticalIndex n) :
    -(n:ℤ) ≤ z.1.1 ∧ z.1.1 ≤ n ∧ -(n:ℤ) ≤ z.1.2 ∧ z.1.2 < n ∧
      -((n^5:ℕ):ℤ) ≤ z.2 ∧ z.2 ≤ (n^5:ℕ) := by
  simp_all [coverVerticalIndex, coverVerticalBase, coverSheets]

 theorem coverHorizontalRawPair_mem (hz : z ∈ coverHorizontalIndex n) :
    (coverHorizontalRawPair z).1 ∈ parafermionicCoverBoxVertices n ∧
      (coverHorizontalRawPair z).2 ∈ parafermionicCoverBoxVertices n := by
  rcases coverHorizontalIndex_bounds n z hz with
    ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi,hbad⟩
  have hshift : parafermionicCoverSheetShift z.1 (z.1.1+1,z.1.2) =
      if z.1.1=0 ∧ z.1.2<0 then 1 else 0 := by
    grind [parafermionicCoverSheetShift]
  change ((z.1,z.2) ∈ parafermionicCoverBoxVertices n) ∧
    (parafermionicCoverNeighborLift (z.1,z.2) (z.1.1+1,z.1.2) ∈
      parafermionicCoverBoxVertices n)
  constructor
  · rw [parafermionicCoverBoxVertices_mem]
    grind
  · rw [parafermionicCoverBoxVertices_mem]
    grind [parafermionicCoverNeighborLift]

 theorem coverVerticalRawPair_mem (hz : z ∈ coverVerticalIndex n) :
    (coverVerticalRawPair z).1 ∈ parafermionicCoverBoxVertices n ∧
      (coverVerticalRawPair z).2 ∈ parafermionicCoverBoxVertices n := by
  rcases coverVerticalIndex_bounds n z hz with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi⟩
  change ((z.1,z.2) ∈ parafermionicCoverBoxVertices n) ∧
    (parafermionicCoverNeighborLift (z.1,z.2) (z.1.1,z.1.2+1) ∈
      parafermionicCoverBoxVertices n)
  constructor
  · rw [parafermionicCoverBoxVertices_mem]
    grind
  · rw [parafermionicCoverBoxVertices_mem]
    grind [parafermionicCoverNeighborLift, parafermionicCoverSheetShift]
end

def coverVerticalPairs (n : ℕ) : Finset
    (ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n) :=
  (coverForwardPairFinset n).filter fun p => p.1.1.1.2 + 1 = p.2.1.1.2

section
variable (n : ℕ) (z : LatticeVertex × ℤ) (hz : z ∈ coverVerticalIndex n)
def verticalIndexPair  :
    ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n :=
  ⟨⟨(coverVerticalRawPair z).1, (coverVerticalRawPair_mem n z hz).1⟩,
   ⟨(coverVerticalRawPair z).2, (coverVerticalRawPair_mem n z hz).2⟩⟩

theorem verticalIndexPair_mem  : verticalIndexPair n z hz ∈
      coverVerticalPairs n := by
  unfold coverVerticalPairs
  simp
  constructor
  · simp only [coverForwardPairFinset, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_, ?_⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · change parafermionicCoverGraph.Adj (z.1,z.2)
        (parafermionicCoverNeighborLift (z.1,z.2) (z.1.1,z.1.2+1))
      apply parafermionicCoverNeighborLift_adj
      rw [squareLattice_adj_iff]
      simp
  rfl
end

section
variable (n : ℕ)
theorem coverVerticalIndex_card_bij  :
    (coverVerticalIndex n).card = (coverVerticalPairs n).card := by
  apply Finset.card_bij (fun z hz => verticalIndexPair n z hz)
  · exact verticalIndexPair_mem n
  · intro a ha b hb hab
    have h := congrArg (fun p : ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n => p.1.1) hab
    tauto
  · intro p hp
    simp only [coverVerticalPairs, Finset.mem_filter] at hp
    have hparts : parafermionicCoverForward p.1.1 p.2.1 ∧
        (parafermionicCoverBoxGraph n).Adj p.1 p.2 := by
      grind [coverForwardPairFinset]
    have hbase : p.2.1.1.1 = p.1.1.1.1 ∧ p.2.1.1.2 = p.1.1.1.2+1 := by
      rcases hparts.1 with hh | hv <;> omega
    have hadj : parafermionicCoverGraph.Adj p.1.1 p.2.1 := hparts.2
    have hsecond : p.2.1 = parafermionicCoverNeighborLift p.1.1
        (p.1.1.1.1,p.1.1.1.2+1) := by
      apply parafermionicCoverNeighborLift_unique
      · grind
      omega
    let z := ((p.1.1.1.1,p.1.1.1.2),p.1.1.2)
    have hz : z ∈ coverVerticalIndex n := by
      simp only [coverVerticalIndex, coverVerticalBase, coverSheets, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_Ico]
      rcases (parafermionicCoverBoxVertices_mem n p.1.1).mp p.1.2 with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi⟩
      rcases (parafermionicCoverBoxVertices_mem n p.2.1).mp p.2.2 with ⟨_,_,_,hyhi2,_,_⟩
      grind
    refine ⟨z,hz,?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [verticalIndexPair, coverVerticalRawPair, z, hsecond]

def coverHorizontalPairs  : Finset
    (ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n) :=
  (coverForwardPairFinset n).filter fun p => p.1.1.1.1 + 1 = p.2.1.1.1

def horizontalIndexPair (z : LatticeVertex × ℤ)
    (hz : z ∈ coverHorizontalIndex n) :
    ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n :=
  ⟨⟨(coverHorizontalRawPair z).1, (coverHorizontalRawPair_mem n z hz).1⟩,
   ⟨(coverHorizontalRawPair z).2, (coverHorizontalRawPair_mem n z hz).2⟩⟩

theorem horizontalIndexPair_mem (z : LatticeVertex × ℤ)
    (hz : z ∈ coverHorizontalIndex n) : horizontalIndexPair n z hz ∈
      coverHorizontalPairs n := by
  unfold coverHorizontalPairs
  simp
  constructor
  · simp only [coverForwardPairFinset, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_, ?_⟩
    · tauto
    · change parafermionicCoverGraph.Adj (z.1,z.2)
        (parafermionicCoverNeighborLift (z.1,z.2) (z.1.1+1,z.1.2))
      apply parafermionicCoverNeighborLift_adj
      rw [squareLattice_adj_iff]
      simp
  rfl

theorem coverHorizontalIndex_card_bij  :
    (coverHorizontalIndex n).card = (coverHorizontalPairs n).card := by
  apply Finset.card_bij (fun z hz => horizontalIndexPair n z hz)
  · exact horizontalIndexPair_mem n
  · intro a ha b hb hab
    have h := congrArg (fun p : ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n => p.1.1) hab
    tauto
  · intro p hp
    simp only [coverHorizontalPairs, Finset.mem_filter] at hp
    have hparts :
        parafermionicCoverForward p.1.1 p.2.1 ∧
        (parafermionicCoverBoxGraph n).Adj p.1 p.2 := by
      grind [coverForwardPairFinset]
    have hbase : p.2.1.1.1 = p.1.1.1.1+1 ∧ p.2.1.1.2 = p.1.1.1.2 := by
      rcases hparts.1 with hh | hv <;> omega
    have hadj : parafermionicCoverGraph.Adj p.1.1 p.2.1 := hparts.2
    have hshift := parafermionicCover_sheetShift_of_adj hadj
    have hsecond : p.2.1 = parafermionicCoverNeighborLift p.1.1
        (p.1.1.1.1+1,p.1.1.1.2) := by
      apply parafermionicCoverNeighborLift_unique
      · grind
      omega
    let z := ((p.1.1.1.1,p.1.1.1.2),p.1.1.2)
    have hz : z ∈ coverHorizontalIndex n := by
      simp only [coverHorizontalIndex, Finset.mem_sdiff, Finset.mem_product,
        coverHorizontalBase, coverSheets, Finset.mem_Ico, Finset.mem_Icc,
        coverHorizontalBad, Finset.mem_singleton]
      rcases (parafermionicCoverBoxVertices_mem n p.1.1).mp p.1.2 with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi⟩
      rcases (parafermionicCoverBoxVertices_mem n p.2.1).mp p.2.2 with ⟨_,hxhi2,_,_,_,hkhi2⟩
      grind [parafermionicCoverSheetShift]
    refine ⟨z, hz, ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [horizontalIndexPair, coverHorizontalRawPair, z, hsecond]

theorem coverForwardPairFinset_eq_union  :
    coverForwardPairFinset n = coverHorizontalPairs n ∪ coverVerticalPairs n := by
  ext p
  simp only [coverHorizontalPairs, coverVerticalPairs, Finset.mem_union,
    Finset.mem_filter, coverForwardPairFinset]
  constructor
  · rintro ⟨_,hf,ha⟩
    rcases hf with hh | hv
    · left
      exact ⟨⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        Or.inl hh,ha⟩, by omega⟩
    · right
      exact ⟨⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        Or.inr hv,ha⟩, by omega⟩
  · grind

theorem coverHorizontalVertical_disjoint  :
    Disjoint (coverHorizontalPairs n) (coverVerticalPairs n) := by
  apply Finset.disjoint_left.mpr
  grind [coverHorizontalPairs, coverVerticalPairs, parafermionicCoverForward, parafermionicCoverBoxGraph, coverForwardPairFinset]

 theorem parafermionicCoverBoxGraph_edgeFinset_card_add_n (hn : 0 < n) :
    (parafermionicCoverBoxGraph n).edgeFinset.card + n =
      4*n*(2*n+1)*(2*n^5+1) := by
  rw [← (coverForwardPairFinset_card_eq_edgeFinset_card n), coverForwardPairFinset_eq_union,
    Finset.card_union_of_disjoint (coverHorizontalVertical_disjoint n),
    ← coverHorizontalIndex_card_bij, ← coverVerticalIndex_card_bij,
    coverHorizontalIndex_card, coverVerticalIndex_card]
  grind
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
