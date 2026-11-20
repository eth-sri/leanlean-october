/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsDiscontinuity.FK

/-- In a finite graph, an odd total degree on `B` forces a path from `B` to `T`
when every vertex outside the two sets has even degree. -/
theorem exists_reachable_between_of_odd_degree_sum
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (B T : Finset V)
    (heven : ∀ v, v ∉ (B ∪ T) → Even (G.degree v))
    (hodd : Odd (∑ v ∈ B, G.degree v)) :
    ∃ b ∈ B, ∃ t ∈ T, G.Reachable b t := by
  classical
  by_contra hgoal
  have hno (b : V) (hb : b ∈ B) (t : V) (ht : t ∈ T) :
      ¬ G.Reachable b t := by
    simp_all
  let S : Finset V := Finset.univ.filter fun v => ∃ b ∈ B, G.Reachable b v
  have memS (v : V) : v ∈ S ↔ ∃ b ∈ B, G.Reachable b v := by
    simp [S]
  have hBsub : B ⊆ S := by
    intro b hb
    rw [memS]
    exact ⟨b, hb, SimpleGraph.Reachable.refl b⟩
  have hclosed {u v : V} (hu : u ∈ S) (hadj : G.Adj u v) : v ∈ S := by
    rw [memS] at hu ⊢
    rcases hu with ⟨b, hb, hreach⟩
    exact ⟨b, hb, hreach.trans hadj.reachable⟩
  have hdegreeSumS : Even (∑ v ∈ S, G.degree v) := by
    let Ss : Set V := (S : Set V)
    let subtypeFintype : Fintype {x // x ∈ Ss} := Subtype.fintype _
    have hsum :
        (∑ v ∈ S, G.degree v) =
          ∑ v : {x // x ∈ Ss}, (G.induce Ss).degree v := by
      have hatt : S.attach = (Finset.univ : Finset {x // x ∈ Ss}) := by
        ext v
        simp
      rw [← Finset.sum_attach, hatt]
      apply Finset.sum_congr rfl
      intro v hv
      have hneighbors : G.neighborSet (v : V) ⊆ Ss := by
        intro z hz
        exact hclosed v.property ((G.mem_neighborSet (v : V) z).mp hz)
      exact (G.degree_induce_of_neighborSet_subset hneighbors).symm
    rw [hsum, (G.induce Ss).sum_degrees_eq_twice_card_edges]
    simp
  have hrest : Even (∑ v ∈ (S \ B), G.degree v) := by
    apply Finset.even_sum
    intro v hv
    rcases Finset.mem_sdiff.1 hv with ⟨hvS, hvB⟩
    obtain ⟨b, hb, hreach⟩ := (memS v).1 hvS
    exact heven v (by simp [hvB, show v ∉ T from fun ht => hno b hb v ht hreach])
  have hsum : Even ((∑ v ∈ (S \ B), G.degree v) + ∑ v ∈ B, G.degree v) := by
    rwa [Finset.sum_sdiff hBsub]
  exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_add.1 hsum).1 hrest)

end PottsDiscontinuity.FK
