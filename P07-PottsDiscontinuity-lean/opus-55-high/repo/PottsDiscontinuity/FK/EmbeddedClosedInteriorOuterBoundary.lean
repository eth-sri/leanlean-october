/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.FK.ComponentBoundarySupport
public import PottsDiscontinuity.FK.IsolatedBoundaryComponents
public import PottsDiscontinuity.FK.SubgraphComparison

public section

namespace PottsDiscontinuity.FK

noncomputable section

theorem removedEdge_endpoint_not_image_compl_general
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
    (_hGH : G.map f ≤ H) (B : Set V)
    (hclosed : ∀ ⦃x : V⦄, x ∉ B → ∀ ⦃y : W⦄, H.Adj (f x) y →
      ∃ z : V, f z = y ∧ G.Adj x z)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
    ∀ ⦃e : H.edgeSet⦄, e ∈ K.val → ∀ ⦃w : W⦄, w ∈ e.1 →
      w ∉ f '' Bᶜ := by
  intro e he w hw himage
  rcases himage with ⟨x, hxB, hfx⟩
  have hnot :=
    (mem_subgraphRemovedEdges e).mp (K.property he)
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e.1
  have heval : e.1 = Sym2.mk a b := by simp_all
  have habAdj : H.Adj a b := by
    apply H.mem_edgeSet.mp
    grind
  have hwAB : w = a ∨ w = b := by
    simp_all
  rcases hwAB with hwa | hwb
  · obtain ⟨z, hzb, hxz⟩ := hclosed hxB (by simpa [(hfx.trans hwa)] using habAdj)
    aesop
  · obtain ⟨z, hza, hxz⟩ := hclosed hxB (by simpa [(hfx.trans hwb)] using habAdj.symm)
    have he' : e.1 = Sym2.mk (f x) (f z) := by
      grind
    aesop

/-- Frozen configurations in an exterior region pull back to a partition
finer than the partition wiring `B`, for any outer boundary whose boundary
points avoid the embedded complement of `B`. Neighbor closure ensures frozen
removed edges cannot identify a point in that complement. -/
theorem isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
    (hGH : G.map f ≤ H) (B : Set V)
    (hclosed : ∀ ⦃x : V⦄, x ∉ B → ∀ ⦃y : W⦄, H.Adj (f x) y →
      ∃ z : V, f z = y ∧ G.Adj x z)
    (ξ : BoundaryCondition W)
    (hξavoid : ∀ ⦃x : V⦄, x ∉ B → f x ∉ ξ.boundary)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
    (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition ≤
      (BoundaryCondition.wired B).partition := by
  let D := (f '' Bᶜ)ᶜ
  have hcomp :=
    componentSetoid_le_wired_union_of_edge_endpoints ξ D K.val (by
      grind [removedEdge_endpoint_not_image_compl_general])
  intro x y hxy
  have houter : (componentSetoid H ξ K.val).r (f x) (f y) :=
    by tauto
  rcases (BoundaryCondition.wired_rel (ξ.boundary ∪ D) (f x) (f y)).mp (hcomp houter) with
    heq | ⟨hx, hy⟩
  · simp_all
  · have hxB : x ∈ B := by
      grind
    have hyB : y ∈ B := by
      grind
    simp_all

end
end PottsDiscontinuity.FK
