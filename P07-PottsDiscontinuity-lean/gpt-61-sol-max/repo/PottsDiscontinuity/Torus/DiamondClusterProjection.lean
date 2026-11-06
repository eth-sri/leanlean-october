module
public import Mathlib

public import PottsDiscontinuity.Torus.DiamondCycleExtension
public import PottsDiscontinuity.Torus.DiamondIntersectionDeterminant

/-!
# Projecting conserved flows to individual open clusters

The incidence endpoints of an open indexed edge belong to one cluster. Restricting
a chain to that cluster preserves conservation, since every corner of each primal
vertex has the same cluster label.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

theorem ribbonIntersection_mul_area_subgraph (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) (f g : diamondCycleSpace hN hM A) :
    (N * M : ℚ) * ribbonIntersection hN hM A f g =
      diamondHorizontalDisplacement A f.val * diamondVerticalDisplacement A g.val -
        diamondVerticalDisplacement A f.val * diamondHorizontalDisplacement A g.val := by
  
  simpa only [ribbonIntersection_fullExtension, diamondHorizontalDisplacement_fullExtension,
    diamondVerticalDisplacement_fullExtension] using  ribbonIntersection_mul_area hN hM hNp hMp
                                                        (fullDiamondCycleExtension hN hM A f) (fullDiamondCycleExtension hN hM A g) 

/-- The actual open cluster carrying an indexed open edge. -/
def diamondEdgeCluster (hN : Even N) (hM : Even M) (A : RCConfig N M) (e : OpenDiamondEdge A)  :=
  (diamondOpenGraph hN hM true A).connectedComponentMk (faceEndpoint hN hM true e.val false)

/-- The open primal cluster incident to a ribbon corner. -/
def ribbonCornerCluster (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (d : DirectedDart (checkerArrows N M)) :
    (diamondOpenGraph hN hM true A).ConnectedComponent :=
  (diamondOpenGraph hN hM true A).connectedComponentMk (ribbonFace hN hM d)

section

variable (hN : Even N) (hM : Even M) (A : RCConfig N M)


theorem ribbonCornerCluster_end 
    (e : OpenDiamondEdge A) (b : Bool) :
    ribbonCornerCluster hN hM A (ribbonEndEquiv hN hM (e.val, b)) = diamondEdgeCluster hN hM A e := by
  unfold ribbonCornerCluster
  rw [ribbonFace_end]
  cases b
  · rfl
  · exact (SimpleGraph.ConnectedComponent.sound
      (diamond_endpoints_reachable hN hM A e.val e.property)).symm

theorem ribbonCornerCluster_corner 
    (v : FaceVertex N M true) (p : Port) :
    ribbonCornerCluster hN hM A (ribbonCornerEquiv hN hM (v, p)) =
      (diamondOpenGraph hN hM true A).connectedComponentMk v := by
  unfold ribbonCornerCluster
  congr 1
  exact Subtype.ext (leftFace_faceCorner v.val p)

end

/-- Restrict an indexed chain to the edges of one actual open cluster. -/
noncomputable def diamondClusterChain (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f : OpenDiamondEdge A → ℚ) :
    OpenDiamondEdge A → ℚ := by
  classical
  exact fun e => if diamondEdgeCluster hN hM A e = c then f e else 0

open scoped Classical in
theorem diamondClusterChain_apply (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f : OpenDiamondEdge A → ℚ)
    (e : OpenDiamondEdge A) : diamondClusterChain hN hM A c f e =
      if diamondEdgeCluster hN hM A e = c then f e else 0 := rfl

open scoped Classical in
theorem ribbonHalfFlow_clusterChain (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f : OpenDiamondEdge A → ℚ)
    (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM A (diamondClusterChain hN hM A c f) d =
      if ribbonCornerCluster hN hM A d = c then ribbonHalfFlow hN hM A f d else 0 := by
  obtain ⟨⟨v, b⟩, rfl⟩ := (ribbonEndEquiv hN hM).surjective d
  rw [ribbonHalfFlow_end, ribbonHalfFlow_end]
  cases ha : A v
  · simp_all
  · rw [extendDiamondChain_open A _ v ha, diamondClusterChain_apply, ribbonCornerCluster_end hN hM A ⟨v, ha⟩ b]
    all_goals aesop

theorem diamondClusterChain_mem (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f : diamondCycleSpace hN hM A) :
    diamondClusterChain hN hM A c f.val ∈ diamondCycleSpace hN hM A := by
  classical
  rw [diamondCycleSpace_mem_iff_corners]
  intro v
  simp_rw [ribbonHalfFlow_clusterChain, ribbonCornerCluster_corner]
  rw [Finset.sum_ite_irrel, sum_ribbonHalfFlow_corners hN hM A f v]
  simp only [Finset.sum_const_zero, ite_self]

/-- The conserved flow carried by one component of an actual conserved flow. -/
noncomputable def diamondClusterCycle (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f : diamondCycleSpace hN hM A) :
    diamondCycleSpace hN hM A :=
  ⟨diamondClusterChain hN hM A c f.val, diamondClusterChain_mem hN hM A c f⟩

end PottsDiscontinuity.Torus
