/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

public section

namespace PottsDiscontinuity.FK

/-- In a finite graph, an odd total degree on `B` forces a path from `B` to `T`
when every vertex outside the two sets has even degree. -/
theorem exists_reachable_between_of_odd_degree_sum
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (B T : Finset V)
    (hdisj : Disjoint B T)
    (heven : ∀ v, v ∉ (B ∪ T) → Even (G.degree v))
    (hodd : Odd (∑ v ∈ B, G.degree v)) :
    ∃ b ∈ B, ∃ t ∈ T, G.Reachable b t := by
  classical
  by_contra hgoal
  let S := Finset.univ.filter fun v => ∃ b ∈ B, G.Reachable b v
  have memS (v : V) : v ∈ S ↔ ∃ b ∈ B, G.Reachable b v := by
    grind
  have hBsub : B ⊆ S := by
    intro b hb
    rw [memS]
    tauto
  have hclosed {u v : V} (hu : u ∈ S) (hadj : G.Adj u v) : v ∈ S := by
    simp_all
    rcases hu with ⟨b, hb, hreach⟩
    exact ⟨b, hb, hreach.trans hadj.reachable⟩
  have hdegreeSumS : Even (∑ v ∈ S, G.degree v) := by
    let Ss := (S : Set V)
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
  have hevenSum : ∀ U : Finset V,
      (∀ v ∈ U, Even (G.degree v)) → Even (∑ v ∈ U, G.degree v) := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert x U hx ih =>
        grind
  have hdecomp :=
    Finset.sum_sdiff hBsub (f := fun v => G.degree v)
  have hB_even : Even (∑ v ∈ B, G.degree v) := by
    grind
  have hnotEven : ¬ Even (∑ v ∈ B, G.degree v) := by
    grind
  exact hnotEven hB_even

end PottsDiscontinuity.FK
