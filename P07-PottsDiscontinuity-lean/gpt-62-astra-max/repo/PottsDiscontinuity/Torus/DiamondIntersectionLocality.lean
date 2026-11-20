module

public import PottsDiscontinuity.Torus.DiamondClusterProjection

/-!
# Intersection localizes to one open cluster

Corner primitives and edge coefficients restrict with the cluster of their vertex.
Hence the global intersection is the sum of pairings within individual clusters.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

open scoped Classical in
@[simp] theorem diamondClusterCycle_apply (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f : diamondCycleSpace hN hM A)
    (e : OpenDiamondEdge A) : (diamondClusterCycle c f).val e =
      if diamondEdgeCluster hN hM e = c then f.val e else 0 := rfl

open scoped Classical in
theorem ribbonCornerPrimitive_clusterCycle (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f : diamondCycleSpace hN hM A)
    (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive (diamondClusterCycle c f) d =
      if ribbonCornerCluster hN hM A d = c then ribbonCornerPrimitive f d else 0 := by
  obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  rw [ribbonCornerPrimitive_corner, ribbonCornerPrimitive_corner]
  change cornerPrimitiveValue (fun q => ribbonHalfFlow hN hM
    (diamondClusterChain c f.val) (ribbonCornerEquiv hN hM (v, q))) p = _
  simp_rw [ribbonHalfFlow_clusterChain, ribbonCornerCluster_corner]
  by_cases hc : (diamondOpenGraph hN hM true A).connectedComponentMk v = c
  · simp [hc, ite_true]
  · simp only [hc, ite_false]
    cases p <;> simp only [cornerPrimitiveValue, neg_zero, sub_zero]

open scoped Classical in
theorem ribbonIntersectionCoefficient_clusterCycle (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (f : diamondCycleSpace hN hM A) (e : OpenDiamondEdge A) :
    ribbonIntersectionCoefficient (diamondClusterCycle c f) e =
      if diamondEdgeCluster hN hM e = c then ribbonIntersectionCoefficient f e else 0 := by
  unfold ribbonIntersectionCoefficient
  rw [ribbonCornerPrimitive_clusterCycle, ribbonCornerPrimitive_clusterCycle,
    ribbonCornerCluster_end hN hM e true, ribbonCornerCluster_end hN hM e false,
    diamondClusterCycle_apply]
  grind

open scoped Classical in
theorem ribbonIntersection_clusterCycles (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f g : diamondCycleSpace hN hM A) :
    ribbonIntersection (diamondClusterCycle c f) (diamondClusterCycle c g) =
      ∑ e : OpenDiamondEdge A, if diamondEdgeCluster hN hM e = c then
        ribbonIntersectionCoefficient f e * g.val e else 0 := by
  apply Finset.sum_congr rfl
  intro e _
  rw [ribbonIntersectionCoefficient_clusterCycle, diamondClusterCycle_apply]
  grind

variable (hN : Even N) (hM : Even M) (A : RCConfig N M)

/-- A nonzero intersection is witnessed by two conserved flows within a single actual cluster. -/
theorem exists_cluster_intersection_nonzero
    (f g : diamondCycleSpace hN hM A) (hfg : ribbonIntersection f g ≠ 0) :
    ∃ c : (diamondOpenGraph hN hM true A).ConnectedComponent,
      ribbonIntersection (diamondClusterCycle c f) (diamondClusterCycle c g) ≠ 0 := by
  classical
  have hs : (∑ c : (diamondOpenGraph hN hM true A).ConnectedComponent,
      ribbonIntersection (diamondClusterCycle c f) (diamondClusterCycle c g)) =
        ribbonIntersection f g := by
    simp_rw [ribbonIntersection_clusterCycles]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ribbonIntersection]
  by_contra hn
  simp_all

/-- A conserved flow is carried entirely by the specified actual open cluster. -/
def SupportedOnDiamondCluster {hN : Even N} {hM : Even M} {A : RCConfig N M}
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f : diamondCycleSpace hN hM A) : Prop :=
  ∀ e : OpenDiamondEdge A, diamondEdgeCluster hN hM e ≠ c → f.val e = 0

theorem diamondClusterCycle_supported
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f : diamondCycleSpace hN hM A) :
    SupportedOnDiamondCluster c (diamondClusterCycle c f) := by
  classical
  intro e he
  simp [diamondClusterCycle_apply, he, ite_false]

end PottsDiscontinuity.Torus
