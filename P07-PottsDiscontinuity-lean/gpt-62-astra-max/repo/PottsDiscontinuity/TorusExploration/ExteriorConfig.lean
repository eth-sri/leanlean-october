module

public import PottsDiscontinuity.TorusTopology.IndexedWalk

/-! Removing an entire actual cluster from an indexed configuration. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus TorusTopology
variable {N M : ℕ}
noncomputable section
open scoped Classical

variable (hN : Even N) (hM : Even M)

lemma corner_edgeCluster (A : RCConfig N M)
    (v : FaceVertex N M true) (p : Port)
    (he : A (faceCorner v.val p).1 = true) :
    diamondEdgeCluster hN hM ⟨(faceCorner v.val p).1,he⟩ =
      (diamondOpenGraph hN hM true A).connectedComponentMk v := by
  let d := ribbonCornerEquiv hN hM (v,p)
  obtain ⟨⟨w,b⟩,hd⟩ := (ribbonEndEquiv hN hM).surjective d
  have hw : w = (faceCorner v.val p).1 := by
    have hh := congrArg (fun x : DirectedDart (checkerArrows N M) => x.val.1) hd
    assumption
  subst w
  have hh := ribbonCornerCluster_end hN hM ⟨(faceCorner v.val p).1,he⟩ b
  rw [hd] at hh
  exact hh.symm.trans (ribbonCornerCluster_corner hN hM A v p)

/-- An indexed path's extended chain vanishes on every corner at a vertex
outside its starting cluster. -/
lemma path_extension_zero_at_exterior
    {A : RCConfig N M} {u v : FaceVertex N M true}
    (p : IndexedWalk hN hM A u v) (w : FaceVertex N M true)
    (hw : (diamondOpenGraph hN hM true A).connectedComponentMk w ≠
      (diamondOpenGraph hN hM true A).connectedComponentMk u) (c : Port) :
    fullDiamondChainExtension p.chain ⟨(faceCorner w.val c).1,rfl⟩ = 0 := by
  change extendDiamondChain p.chain _ = 0
  cases he : A (faceCorner w.val c).1 with
  | false => exact extendDiamondChain_closed _ he
  | true =>
    rw [extendDiamondChain_open _ he]
    apply p.chain_supported
    rwa [corner_edgeCluster hN hM A w c he]

end
end PottsDiscontinuity.TorusExploration
