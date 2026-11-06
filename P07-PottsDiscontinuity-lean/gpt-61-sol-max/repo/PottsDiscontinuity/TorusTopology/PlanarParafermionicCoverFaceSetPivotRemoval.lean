/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarFiniteTriangularPivotReachability
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFacePivotBypass
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetPivots
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceUnionConnectivity

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial




/-- The actual selected-face union graph after deleting precisely its selected
top-pivot edges, on the same original box-vertex carrier. -/
noncomputable def parafermionicCoverFiniteFaceSetWithoutPivotsGraph {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    SimpleGraph (ParafermionicCoverBoxVertex n) :=
  (parafermionicCoverFiniteFaceUnionGraph S).deleteEdges
    (parafermionicCoverFiniteFaceSetPivots S : Set _)

theorem parafermionicCoverFiniteFaceSetWithoutPivotsGraph_reachable_eq
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    (parafermionicCoverFiniteFaceSetWithoutPivotsGraph S).Reachable =
      (parafermionicCoverFiniteFaceUnionGraph S).Reachable := by
  
  let I := {i : ParafermionicCoverFiniteFaceTopIndex n // i ∈ S}
  let U := parafermionicCoverFiniteFaceUnionGraph S
  let F : I → SimpleGraph (ParafermionicCoverBoxVertex n) :=
    fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1.1 i.1.2
  let p : I → Sym2 (ParafermionicCoverBoxVertex n) :=
    fun i => parafermionicCoverFiniteFaceTopPivot n i.1
  
  
  
  
  have hrange : Set.range p =
      (parafermionicCoverFiniteFaceSetPivots S ) := by
    ext e
    simp only [Finset.mem_coe, parafermionicCoverFiniteFaceSetPivots, Finset.mem_image]
    constructor
    · grind
    · aesop
  have hreach := finiteTriangularPivotReachability U F p (fun i => parafermionicCoverFiniteFaceTopRank n i.1) (fun i v w hadj => ⟨i.1, i.2, hadj⟩) (by
                                                                      intro i j hj
                                                                      have hclass := parafermionicCoverFiniteFacePivot_boundary_classification
                                                                        i.1 j.1 (by simpa  using hj)
                                                                      grind) (by
                                                                           intro i
                                                                           simpa  using parafermionicCoverFiniteFaceTopPivot_bypass i.1)
  simpa [parafermionicCoverFiniteFaceSetWithoutPivotsGraph, hrange] using hreach

end PottsDiscontinuity.TorusTopology.Planar.Medial
