module

public import PottsDiscontinuity.Torus.DiamondCycleExtension

/-!
# Projecting conserved flows to individual open clusters

The incidence endpoints of an open indexed edge belong to one cluster.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section

variable (hN : Even N) (hM : Even M) (A : RCConfig N M)

/-- The actual open cluster carrying an indexed open edge. -/
def diamondEdgeCluster (e : OpenDiamondEdge A) :
    (diamondOpenGraph hN hM true A).ConnectedComponent :=
  (diamondOpenGraph hN hM true A).connectedComponentMk (faceEndpoint hN hM true e.val false)

/-- The open primal cluster incident to a ribbon corner. -/
def ribbonCornerCluster
    (d : DirectedDart (checkerArrows N M)) :
    (diamondOpenGraph hN hM true A).ConnectedComponent :=
  (diamondOpenGraph hN hM true A).connectedComponentMk (ribbonFace hN hM d)

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

/-- A flow supported in one cluster vanishes on each other cluster. -/
def SupportedOnDiamondCluster (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (f : diamondCycleSpace hN hM A) : Prop :=
  ∀ e : OpenDiamondEdge A, diamondEdgeCluster hN hM A e ≠ c → f.val e = 0

end PottsDiscontinuity.Torus
