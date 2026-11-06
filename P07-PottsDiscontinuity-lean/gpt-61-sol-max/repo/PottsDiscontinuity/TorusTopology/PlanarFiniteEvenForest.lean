/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph

private theorem walk_support_reachable_from {V : Type*} (G : SimpleGraph V)
    {s u v : V} (hus : G.Reachable s u) (p : G.Walk u v) :
    ∀ x ∈ p.support, G.Reachable s x := by
  induction p with
  | nil =>
      simp_all
  | @cons a b c hab p ih =>
      intro x hx
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hus
      · exact ih (hus.trans hab.reachable) x hx

/-- A finite acyclic simple graph with even degree at every vertex has no edges. -/
theorem eq_bot_of_isAcyclic_even_degree
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic) (heven : ∀ v : V, Even (G.degree v)) :
    G = ⊥ := by
  classical
  rw [eq_bot_iff_forall_not_adj]
  intro u v huv
  let C  := {x : V // G.Reachable u x}
  let H : SimpleGraph C := G.induce  (G.Reachable u) 
  let root : C := ⟨u, Reachable.refl u⟩
  have hclosed (x : C) : G.neighborSet x.1 ⊆ {y : V | G.Reachable u y} := by
    intro y hy
    
    exact x.2.trans hy.reachable
  have hdegree (x : C) : H.degree x = G.degree x.1 := by
    dsimp [H, C]
    exact G.degree_induce_of_neighborSet_subset (hclosed x)
  have hconn : H.Connected := by
    apply H.connected_iff_exists_forall_reachable.mpr
    refine ⟨root, ?_⟩
    intro x
    rcases x.2 with ⟨p⟩
    
    exact ⟨p.induce  (G.Reachable u)    (walk_support_reachable_from G (Reachable.refl u) p)  ⟩
  
  have htree : H.IsTree := by
                             solve_by_elim [_root_.SimpleGraph.IsTree.mk, _root_.SimpleGraph.IsAcyclic.induce]
  have hne : v ≠ u := by
    intro h
    subst v
    exact huv.ne rfl
  let rv : C := ⟨v, huv.reachable⟩
  have hrootNe : root ≠ rv := by
    aesop
  let : Nontrivial C := by
                          solve_by_elim [_root_.Nontrivial.mk, _root_.Exists.intro]
  obtain ⟨x, hx⟩ := htree.exists_vert_degree_one_of_nontrivial
  rw [hdegree] at hx
  obtain ⟨k, hk⟩ := heven x.1
  rw [hk] at hx
  omega

end PottsDiscontinuity.TorusTopology.Planar.Medial
