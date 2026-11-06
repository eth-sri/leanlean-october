/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsDiscontinuity.FK

/-- In a finite graph, an odd total degree on `B` forces a path from `B` to `T`
when every vertex outside the two sets has even degree. -/
theorem exists_reachable_between_of_odd_degree_sum
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (B T : Finset V)
    (hdisj : Disjoint B T)
    (heven : ∀ v, v ∉  B ∪ T  → Even (G.degree v))
    (hodd : Odd (∑ v ∈ B, G.degree v)) :
    ∃ b ∈ B, ∃ t ∈ T, G.Reachable b t := by
  
  
  
  let S  := Finset.univ.filter fun v => ∃ b ∈ B, G.Reachable b v
  have memS (v : V) : v ∈ S ↔ ∃ b ∈ B, G.Reachable b v := by
    simp [S]
  
  have hclosed {u v : V} (hu : u ∈ S) (hadj : G.Adj u v) : v ∈ S := by
    rw [memS] at hu ⊢
    rcases hu with ⟨b, hb, hreach⟩
    exact ⟨b, hb, hreach.trans hadj.reachable⟩
  
  have hdegreeSumS : Even (∑ v ∈ S, G.degree v) := by
    let Ss : Set V := S
    let subtypeFintype : Fintype {x // x ∈ Ss} := Subtype.fintype _
    
    rw [(by
           have hatt : S.attach = (Finset.univ ) := by
             ext v
             simp 
           rw [← Finset.sum_attach]
           rw [hatt]
           apply Finset.sum_congr rfl
           intro v hv
           have hneighbors : G.neighborSet v ⊆ Ss := by
             intro z hz
             exact hclosed v.property ((G.mem_neighborSet v z).mp hz)
           exact (G.degree_induce_of_neighborSet_subset hneighbors).symm :
         ∑ v ∈ S, G.degree v  =
          ∑ v : {x // x ∈ Ss}, (G.induce Ss).degree v), (G.induce Ss).sum_degrees_eq_twice_card_edges]
    exact ⟨(G.induce Ss).edgeFinset.card, by omega⟩
  have hevenSum : ∀ U ,
      (∀ v ∈ U, Even (G.degree v)) → Even (∑ v ∈ U, G.degree v) := by
                                                                     solve_by_elim [_root_.Finset.even_sum]
  
  have hdecomp  :=
    Finset.sum_sdiff (by
                        intro b hb
                        rw [memS]
                        exact ⟨b, hb, SimpleGraph.Reachable.refl b⟩) (f := fun v => G.degree v)
  grind

end PottsDiscontinuity.FK
