module

public import PottsDiscontinuity.TorusTopology.IndexedWalk

/-! Removing an entire actual cluster from an indexed configuration. -/

public section

namespace PottsDiscontinuity.TorusExploration
open Torus TorusTopology
variable {N M : ℕ}
noncomputable section
open scoped Classical

section
variable (hN : Even N) (hM : Even M)
theorem corner_edgeCluster (A : RCConfig N M)
    (v : FaceVertex N M true) (p : Port)
    (he : A (faceCorner v.val p).1 = true) :
    diamondEdgeCluster hN hM A ⟨(faceCorner v.val p).1,he⟩ =
      (diamondOpenGraph hN hM true A).connectedComponentMk v := by
  let d := ribbonCornerEquiv hN hM (v,p)
  obtain ⟨⟨w,b⟩,hd⟩ := (ribbonEndEquiv hN hM).surjective d
  have hw : w = (faceCorner v.val p).1 := by
    have hh := congrArg (fun x : DirectedDart (checkerArrows N M) => x.val.1) hd
    tauto
  have hh := ribbonCornerCluster_end hN hM A ⟨(faceCorner v.val p).1,he⟩ b
  simp_all
  exact hh.symm.trans (ribbonCornerCluster_corner hN hM A v p)

/-- An indexed path's extended chain vanishes on every corner at a vertex
outside its starting cluster. -/
theorem path_extension_zero_at_exterior {A : RCConfig N M} {u v : FaceVertex N M true}
    (p : IndexedWalk hN hM A u v) (w : FaceVertex N M true)
    (hw : (diamondOpenGraph hN hM true A).connectedComponentMk w ≠
      (diamondOpenGraph hN hM true A).connectedComponentMk u) (c : Port) :
    fullDiamondChainExtension A p.chain ⟨(faceCorner w.val c).1,rfl⟩ = 0 := by
  change extendDiamondChain A p.chain _ = 0
  cases he : A (faceCorner w.val c).1 with
  | false => simp_all
  | true =>
    rw [extendDiamondChain_open A _ _ he]
    apply p.chain_supported
    simp_all [corner_edgeCluster]
end

end
end PottsDiscontinuity.TorusExploration
