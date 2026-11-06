/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph

section
variable {V : Type*}
theorem walk_support_reachable_from (G : SimpleGraph V)
    {s u v : V} (hus : G.Reachable s u) (p : G.Walk u v) :
    ∀ x ∈ p.support, G.Reachable s x := by
  induction p with
  | nil =>
      simp_all
  | @cons a b c hab p ih =>
      intro x hx
      simp at hx
      rcases hx with rfl | hx
      · omega
      · exact ih (hus.trans hab.reachable) x hx

/-- A finite acyclic simple graph with even degree at every vertex has no edges. -/
theorem eq_bot_of_isAcyclic_even_degree
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic) (heven : ∀ v : V, Even (G.degree v)) :
    G = ⊥ := by
  classical
  rw [eq_bot_iff_forall_not_adj]
  intro u v huv
  let C := {x : V // G.Reachable u x}
  let H : SimpleGraph C := G.induce (fun x : V => G.Reachable u x)
  let root : C := ⟨u, Reachable.refl u⟩
  have hclosed (x : C) : G.neighborSet x.1 ⊆ {y : V | G.Reachable u y} := by
    intro y hy
    exact x.2.trans hy.reachable
  have hdegree (x : C) : H.degree x = G.degree x.1 :=
    G.degree_induce_of_neighborSet_subset (hclosed x)
  have hconn : H.Connected := by
    apply H.connected_iff_exists_forall_reachable.mpr
    refine ⟨root, ?_⟩
    intro x
    rcases x.2 with ⟨p⟩
    exact ⟨p.induce (fun y : V => G.Reachable u y) (fun y hy => (walk_support_reachable_from G (Reachable.refl u) p) y hy)⟩
  have hacyclicH : H.IsAcyclic :=
    hacyclic.induce _
  have htree : H.IsTree := by tauto
  let rv : C := ⟨v, huv.reachable⟩
  have hrootNe : root ≠ rv := by
    grind
  let : Nontrivial C := ⟨⟨root, rv, hrootNe⟩⟩
  obtain ⟨x, hx⟩ := htree.exists_vert_degree_one_of_nontrivial
  simp_all
  obtain ⟨k, hk⟩ := heven x.1
  omega
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
