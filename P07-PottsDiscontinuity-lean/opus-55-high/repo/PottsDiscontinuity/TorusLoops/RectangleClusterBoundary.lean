module

public import PottsDiscontinuity.FK.IsolatedBoundaryComponents
public import PottsDiscontinuity.FK.SubgraphComparison

/-!
# Frozen open edges confined to an explored cluster

If every open edge in the frozen state has both endpoints in the explored
region, no two vertices embedded in its complement become identified by the
induced frozen boundary partition.
-/

public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.FK

/-- An open frozen state supported inside `U` induces free boundary on any
embedded graph whose vertices all lie outside `U`. -/
theorem isolatedExtensionPullbackFrozenFree_of_openEdges_inside
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V ↪ W) (_hGH : G.map f ≤ H)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))
    (U : Set W)
    (hK : ∀ ⦃x y : W⦄, (openGraph H K.val).Adj x y → x ∈ U ∧ y ∈ U)
    (hf : ∀ x : V, f x ∉ U) :
    (isolatedExtensionPullbackBoundary f
      (frozenBoundary (BoundaryCondition.free ∅) K.val)).partition ≤
        (BoundaryCondition.free ∅).partition := by
  intro x y hxy
  change (Setoid.comap f
      (componentSetoid H (BoundaryCondition.free ∅) K.val)).r x y at hxy
  have hrel : (componentSetoid H (BoundaryCondition.free ∅) K.val).r
      (f x) (f y) := by omega
  rw [componentSetoid_free] at hrel
  have hreachable_eq : ∀ {a b : W}, (openGraph H K.val).Reachable a b →
      a ∉ U → a = b := by
    intro a b hab ha
    rw [SimpleGraph.reachable_iff_reflTransGen] at hab
    grind
  have hxy' : f x = f y := by tauto
  simp_all

end PottsDiscontinuity.TorusLoops
