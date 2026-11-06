/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceBoundaryGraph
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFacePivotGeometry
public import PottsDiscontinuity.TorusTopology.PlanarFiniteEvenTriangularElimination
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial







private theorem coverFiniteFacePivot_boundary_classification {n : ℕ}
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

theorem parafermionicCoverFiniteFaceChainDecomposition {n : ℕ} (hn : 1 ≤ n)
    (H : SimpleGraph (ParafermionicCoverBoxVertex n))
    (hle : H ≤ parafermionicCoverBoxGraph n)
    (hHeven : ∀ v, Even (H.neighborSet v).ncard) :
    ∃ L : List (ParafermionicCoverFiniteFaceTopIndex n),
      L.Nodup ∧
      faceSymmDiffList
        (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L = H := by
  classical
  
  
  
  
  
  
  let p  :=
    parafermionicCoverFiniteFaceTopPivot n
  
  
  
  
  
  
  
  
  
  exact exists_faceSymmDiffList_of_even_subgraph
    (parafermionicCoverBoxGraph n) (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) p (parafermionicCoverFiniteFaceTopRank n)
    (fun i => parafermionicCoverFiniteFaceBoundaryGraph_le_boxGraph i.1 i.2) (by
            intro i v
            
            simpa only [parafermionicCoverFiniteFaceBoundaryDegree, SimpleGraph.ncard_neighborSet] using  parafermionicCoverFiniteFaceBoundaryGraph_even_degree i.1 i.2 v ) (by
                   intro i
                   
                   have heq : parafermionicCoverFiniteFaceTopEdgeBox i.1 i.2 = p i := by
                     rfl
                   simpa [heq] using  parafermionicCoverFiniteFaceTopEdgeBox_mem_boundaryGraph i.1 i.2 )  coverFiniteFacePivot_boundary_classification  (parafermionicCoverBoxGraph_deleteTopPivots_isAcyclic n hn) H hle (by
                                           simp_all)

end PottsDiscontinuity.TorusTopology.Planar.Medial
