/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph

private theorem reachable_of_walk_steps {V : Type*} {A R : SimpleGraph V}
    {u v : V} (w : A.Walk u v)
    (hstep : ∀ x y, A.Adj x y → R.Reachable x y) : R.Reachable u v := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons x y z hxy rest ih => exact (hstep x y hxy).trans ih

private theorem reachable_of_sym2_pair {V : Type*} (R : SimpleGraph V)
    {e : Sym2 V} {x y : V} (he : e = s(x,y))
    (h : R.Reachable e.out.1 e.out.2) : R.Reachable x y := by
  have hout : s(e.out.1,e.out.2) = s(x,y) := by
    rw [Sym2.mk, e.out_eq, he]
  rcases Sym2.eq_iff.mp hout with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · simpa [h₁,h₂] using h
  · simpa [h₁,h₂] using h.symm

/-- If every pivot edge has an alternate path in its own face after that pivot
is removed, and every other pivot in that face has smaller rank, deleting all
pivots preserves ambient reachability. -/
theorem finiteTriangularPivotReachability
    {V I : Type*} (G : SimpleGraph V)
    (F : I → SimpleGraph V) (p : I → Sym2 V) (rank : I → ℕ)
    (hsub : ∀ i, F i ≤ G)
    (htri : ∀ i j, p j ∈ (F i).edgeSet → j = i ∨ rank j < rank i)
    (halt : ∀ i,
      ((F i).deleteEdges {p i}).Reachable (p i).out.1 (p i).out.2) :
    (G.deleteEdges (Set.range p)).Reachable = G.Reachable := by
  
  let R := G.deleteEdges (Set.range p)
  have hpiv : ∀ i, R.Reachable (p i).out.1 (p i).out.2 := by
    intro i
    have hbyRank : ∀ k, ∀ j, rank j = k → R.Reachable (p j).out.1 (p j).out.2 := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro j hj
        apply (halt j).elim
        intro w
        apply reachable_of_walk_steps w
        intro x y hxy
        have hdel :=  SimpleGraph.deleteEdges_adj.mp hxy 
        have hF  := hdel.1
        have hG  := hsub j hF
        by_cases he : s(x,y) ∈ Set.range p
        · rcases he with ⟨l, hl⟩
          
          have hne : l ≠ j := by
            grind
          have hpl : p l ∈ (F j).edgeSet := by
            simp_all
          have horder := htri j l hpl
          have hlt : rank l < k := by
            simp_all
          have hroute := ih (rank l) hlt l rfl
          exact reachable_of_sym2_pair R hl hroute
        · exact (SimpleGraph.deleteEdges_adj).2 ⟨hG, he⟩ |>.reachable
    exact hbyRank (rank i) i rfl
  
  have hGR : ∀ x y, G.Reachable x y → R.Reachable x y := fun x y hxy => Nonempty.casesOn hxy fun w => reachable_of_walk_steps w (by
                                                                                                                                   intro x y hxy
                                                                                                                                   by_cases he : s(x,y) ∈ Set.range p
                                                                                                                                   · grind [reachable_of_sym2_pair]
                                                                                                                                   · exact (SimpleGraph.deleteEdges_adj).2 ⟨hxy, he⟩ |>.reachable)
  
  ext x y
  exact ⟨(fun x y => Reachable.mono (deleteEdges_le (Set.range p))) x y, hGR x y⟩

end PottsDiscontinuity.TorusTopology.Planar.Medial
