/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module
public import Mathlib

public import Mathlib.Tactic
public import PottsDiscontinuity.FK.ComponentBoundarySupport
public import PottsDiscontinuity.FK.IsolatedBoundaryComponents
public import PottsDiscontinuity.FK.SubgraphComparison

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

section

variable {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
include V W G H f

private theorem removedEdge_endpoint_not_image_compl_general
    
    (_hGH : G.map f ≤ H) (B : Set V)
    (hclosed : ∀ ⦃x : V⦄, x ∉ B → ∀ ⦃y : W⦄, H.Adj (f x) y →
      ∃ z : V, f z = y ∧ G.Adj x z)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
    ∀ ⦃e : H.edgeSet⦄, e ∈ K.val → ∀ ⦃w : W⦄, w ∈ e.1 →
      w ∉ f '' Bᶜ := by
  
  intro e he w hw himage
  rcases himage with ⟨x, hxB, hfx⟩
  have hnot  :=
    (mem_subgraphRemovedEdges e).mp (K.property he)
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e.1
  have heval : e.1 = Sym2.mk a b := Eq.symm hab
  have habAdj : H.Adj a b := by
    apply H.mem_edgeSet.mp
    grind
  
  rcases  by
            rw [heval] at hw
            exact (Sym2.mem_iff').mp hw  with hwa | hwb
  · 
    simp_all <;> grind
  · 
    obtain ⟨z, hza, hxz⟩ := hclosed hxB (by simpa [ hfx.trans hwb ] using habAdj.symm)
    
    have he' : e.1 = Sym2.mk (f x) (f z) := by
      grind
    apply hnot
    rw [he']
    exact (G.map f).mem_edgeSet.mpr ((SimpleGraph.map_adj _ _ _ _).mpr ⟨x, z, hxz, rfl, rfl⟩)

/-- Frozen configurations in an exterior region pull back to a partition
finer than the partition wiring `B`, for any outer boundary whose boundary
points avoid the embedded complement of `B`. Neighbor closure ensures frozen
removed edges cannot identify a point in that complement. -/
theorem isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior
    
    (hGH : G.map f ≤ H) (B : Set V)
    (hclosed : ∀ ⦃x : V⦄, x ∉ B → ∀ ⦃y : W⦄, H.Adj (f x) y →
      ∃ z : V, f z = y ∧ G.Adj x z)
    (ξ : BoundaryCondition W)
    (hξavoid : ∀ ⦃x : V⦄, x ∉ B → f x ∉ ξ.boundary)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
    (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition ≤
      (BoundaryCondition.wired B).partition := by
  
  let D  := (f '' Bᶜ)ᶜ
  
  intro x y hxy
  
  
  rcases (BoundaryCondition.wired_rel (ξ.boundary ∪ D) (f x) (f y)).mp ((componentSetoid_le_wired_union_of_edge_endpoints ξ D K.val (by
                                                                                           grind [removedEdge_endpoint_not_image_compl_general])) ((Setoid.comap_rel f (frozenBoundary ξ K.val).partition x y).mp hxy)) with
    heq | ⟨hx, hy⟩
  · simp_all
  · 
    
    simp_all <;> grind

end

end
end PottsDiscontinuity.FK
