module
public import Mathlib

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
    (e : OpenDiamondEdge A) : (diamondClusterCycle hN hM A c f).val e =
      if diamondEdgeCluster hN hM A e = c then f.val e else 0 := rfl

open scoped Classical in
theorem ribbonCornerPrimitive_clusterCycle (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f : diamondCycleSpace hN hM A)
    (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive hN hM A (diamondClusterCycle hN hM A c f) d =
      if ribbonCornerCluster hN hM A d = c then ribbonCornerPrimitive hN hM A f d else 0 := by
  obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  rw [ribbonCornerPrimitive_corner, ribbonCornerPrimitive_corner]
  change cornerPrimitiveValue (fun q => ribbonHalfFlow hN hM A
    (diamondClusterChain hN hM A c f.val) (ribbonCornerEquiv hN hM (v, q))) p = _
  simp_rw [ribbonHalfFlow_clusterChain, ribbonCornerCluster_corner]
  by_cases hc : (diamondOpenGraph hN hM true A).connectedComponentMk v = c
  · simp only [hc, ite_true]
  · simp only [hc, ite_false]
    cases p <;> simp only [cornerPrimitiveValue, neg_zero, sub_zero]

open scoped Classical in
theorem ribbonIntersectionCoefficient_clusterCycle (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (f : diamondCycleSpace hN hM A) (e : OpenDiamondEdge A) :
    ribbonIntersectionCoefficient hN hM A (diamondClusterCycle hN hM A c f) e =
      if diamondEdgeCluster hN hM A e = c then ribbonIntersectionCoefficient hN hM A f e else 0 := by
  unfold ribbonIntersectionCoefficient
  rw [ribbonCornerPrimitive_clusterCycle, ribbonCornerPrimitive_clusterCycle, ribbonCornerCluster_end hN hM A e true, ribbonCornerCluster_end hN hM A e false]
  all_goals aesop

open scoped Classical in
theorem ribbonIntersection_clusterCycles (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f g : diamondCycleSpace hN hM A) :
    ribbonIntersection hN hM A (diamondClusterCycle hN hM A c f) (diamondClusterCycle hN hM A c g) =
      ∑ e : OpenDiamondEdge A, if diamondEdgeCluster hN hM A e = c then
        ribbonIntersectionCoefficient hN hM A f e * g.val e else 0 := by
  grind [ribbonIntersection, ribbonIntersectionCoefficient_clusterCycle, diamondClusterCycle_apply]

/-- A nonzero intersection is witnessed by two conserved flows within a single actual cluster. -/
theorem exists_cluster_intersection_nonzero (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g : diamondCycleSpace hN hM A) (hfg : ribbonIntersection hN hM A f g ≠ 0) :
    ∃ c : (diamondOpenGraph hN hM true A).ConnectedComponent,
      ribbonIntersection hN hM A (diamondClusterCycle hN hM A c f) (diamondClusterCycle hN hM A c g) ≠ 0 := by
  classical
  
  have hs :  ∑ c : (diamondOpenGraph hN hM true A).ConnectedComponent,
      ribbonIntersection hN hM A (diamondClusterCycle hN hM A c f) (diamondClusterCycle hN hM A c g)  =
        ribbonIntersection hN hM A f g := by
    simp_rw [ribbonIntersection_clusterCycles]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ribbonIntersection]
  by_contra hn
  push Not at hn
  apply hfg
  rw [← hs]
  exact Finset.sum_eq_zero  fun c _ => hn c 

/-- A conserved flow is carried entirely by the specified actual open cluster. -/
def SupportedOnDiamondCluster (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f : diamondCycleSpace hN hM A)  :=
  ∀ e : OpenDiamondEdge A, diamondEdgeCluster hN hM A e ≠ c → f.val e = 0

theorem diamondClusterCycle_supported (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f : diamondCycleSpace hN hM A) :
    SupportedOnDiamondCluster hN hM A c (diamondClusterCycle hN hM A c f) := by
  
  intro e he
  simp_all

end PottsDiscontinuity.Torus
