/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedFaceIncidence

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

section
variable {n : ℕ} (T : Finset (ParafermionicCoverFiniteFaceTopIndex n))
/-- A maximal-height actual face contributes its own top pivot to the
symmetric-difference boundary of the selected actual face family. -/
theorem parafermionicCoverFiniteFaceSetBoundaryGraph_maximal_pivot_mem
    (i : ParafermionicCoverFiniteFaceTopIndex n) (hi : i ∈ T)
    (hmax : ∀ j ∈ T,
      parafermionicCoverFiniteFaceTopRank n j ≤
        parafermionicCoverFiniteFaceTopRank n i) :
    parafermionicCoverFiniteFaceTopPivot n i ∈
      (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet := by
  let e := parafermionicCoverFiniteFaceTopPivot n i
  have hiEdge : e ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
    have hmem := parafermionicCoverFiniteFaceTopEdgeBox_mem_boundaryGraph i.1 i.2
    tauto
  have hselected : i ∈ parafermionicCoverFiniteFaceSelectedIncidentFaces T e := by
    apply Finset.mem_filter.mpr
    grind [parafermionicCoverFiniteFaceIncidentFaces]
  have hsubset :
      parafermionicCoverFiniteFaceSelectedIncidentFaces T e ⊆ {i} := by
    intro j hj
    have hjData : j ∈ T ∧ e ∈
        (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet := by
      grind [parafermionicCoverFiniteFaceSelectedIncidentFaces, parafermionicCoverFiniteFaceIncidentFaces]
    have hclass := parafermionicCoverFiniteFacePivot_boundary_classification j i
      (by grind)
    grind
  have hcard :
      (parafermionicCoverFiniteFaceSelectedIncidentFaces T e).card = 1 := by
    have hle := Finset.card_le_card hsubset
    grind
  exact (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
    T e).2 hcard

/-- Every nonempty finite actual face family has a boundary edge equal to an
actual top pivot of one of its faces. -/
theorem parafermionicCoverFiniteFaceSetBoundaryGraph_exists_pivot
    (hT : T.Nonempty) :
    ∃ i ∈ T, parafermionicCoverFiniteFaceTopPivot n i ∈
      (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet := by
  obtain ⟨i0, hi0⟩ := hT
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image T
    (parafermionicCoverFiniteFaceTopRank n) ⟨i0, hi0⟩
  exact ⟨i, hi,
    parafermionicCoverFiniteFaceSetBoundaryGraph_maximal_pivot_mem T i hi hmax⟩
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
