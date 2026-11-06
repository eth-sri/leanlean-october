/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceChainDecomposition
public import PottsDiscontinuity.TorusTopology.PlanarFiniteTriangularFaceUniqueness
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial





/-- The actual four-edge face support makes its own top pivot unique at its
height; every other top pivot on the boundary has strictly smaller rank. -/
theorem parafermionicCoverFiniteFacePivot_boundary_classification {n : ℕ}
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (hij : parafermionicCoverFiniteFaceTopPivot n j ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet) :
    j = i ∨ parafermionicCoverFiniteFaceTopRank n j <
      parafermionicCoverFiniteFaceTopRank n i := by
  have hraw := Set.mem_image_of_mem (Sym2.map Subtype.val) hij
  rw [parafermionicCoverFiniteFaceBoundaryGraph_actualEdgeSet] at hraw
  
  
  
  rcases hraw with hbottom | hright | htop | hleft
  · 
    exact Or.inr (parafermionicCoverFiniteFaceTopRank_strict_height n (by
                                                                         by_contra hnot
                                                                         
                                                                         exact (parafermionicCoverFiniteFaceBottomEdge_ne_topEdge_of_height_le
                                                                           i.2 j.2 (by omega)) hbottom.symm))
  · exact False.elim ((parafermionicCoverFiniteFaceRightEdge_ne_topEdge
      i.2 j.2) hright.symm)
  · exact Or.inl (Subtype.ext (parafermionicCoverFiniteFaceTopEdge_injective
      n j.2 i.2 htop))
  · exact False.elim ((parafermionicCoverFiniteFaceLeftEdge_ne_topEdge
      i.2 j.2) hleft.symm)

theorem parafermionicCoverFiniteFaceChain_toFinset_unique {n : ℕ}
    (L M : List (ParafermionicCoverFiniteFaceTopIndex n))
    (hL : L.Nodup) (hM : M.Nodup)
    (hEq : faceSymmDiffList
      (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L =
      faceSymmDiffList
      (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) M) :
    L.toFinset = M.toFinset := by
  
  
  
  
  
  
  exact faceSymmDiffList_eq_implies_toFinset_eq (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) (parafermionicCoverFiniteFaceTopPivot n) (parafermionicCoverFiniteFaceTopRank n) (by
                                                            intro i
                                                            have hmem := parafermionicCoverFiniteFaceTopEdgeBox_mem_boundaryGraph i.1 i.2
                                                            aesop)  parafermionicCoverFiniteFacePivot_boundary_classification  L M hL hM
     hEq 

theorem parafermionicCoverFiniteFaceChain_unique_representation {n : ℕ}
    (hn : 1 ≤ n) (H : SimpleGraph (ParafermionicCoverBoxVertex n))
    (hle : H ≤ parafermionicCoverBoxGraph n)
    (hHeven : ∀ v, Even (H.neighborSet v).ncard) :
    ∃! S : Finset (ParafermionicCoverFiniteFaceTopIndex n),
      ∃ L : List (ParafermionicCoverFiniteFaceTopIndex n),
        L.Nodup ∧ L.toFinset = S ∧
          faceSymmDiffList
            (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L = H := by
  
  obtain ⟨L, hL, hLH⟩ := parafermionicCoverFiniteFaceChainDecomposition hn H hle hHeven
  refine ⟨L.toFinset, ⟨L, hL, rfl, hLH⟩, ?_⟩
  intro S hS
  obtain ⟨M, hM, hMS, hMH⟩ := hS
  
  exact ((parafermionicCoverFiniteFaceChain_toFinset_unique L M hL hM
            (hLH.trans hMH.symm)).trans hMS).symm

end PottsDiscontinuity.TorusTopology.Planar.Medial
