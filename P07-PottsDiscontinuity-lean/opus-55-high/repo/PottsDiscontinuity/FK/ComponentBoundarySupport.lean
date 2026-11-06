/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q.
Only the general finite-graph declaration used by the box comparison is extracted. -/
module

public import PottsDiscontinuity.FK.Wiring

public section

namespace PottsDiscontinuity.FK

variable {V : Type*} {G : SimpleGraph V}

theorem componentSetoid_le_wired_union_of_edge_endpoints
    (ξ : BoundaryCondition V) (D : Set V) (A : Configuration G)
    (hA : ∀ ⦃e : G.edgeSet⦄, e ∈ A → ∀ ⦃u : V⦄, u ∈ e.1 → u ∈ D) :
    componentSetoid G ξ A ≤ (BoundaryCondition.wired (ξ.boundary ∪ D)).partition := by
  apply componentSetoid_le
  · apply reachableSetoid_le_of_adj (openGraph G A)
      (BoundaryCondition.wired (ξ.boundary ∪ D)).partition
    intro x y hxy
    rw [openGraph_adj] at hxy
    rcases hxy with ⟨e, heA, hexy⟩
    apply (BoundaryCondition.wired_rel (ξ.boundary ∪ D) x y).2
    grind
  · intro x y hxy
    rcases ξ.supported hxy with rfl | ⟨hx, hy⟩
    · simp
    simp_all

end PottsDiscontinuity.FK
