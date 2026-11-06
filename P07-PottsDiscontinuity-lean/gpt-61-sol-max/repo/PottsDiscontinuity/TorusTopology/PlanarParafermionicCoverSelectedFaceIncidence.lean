/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetBoundary

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

/-- The retained actual faces whose lifted boundaries contain a given actual edge. -/
noncomputable def parafermionicCoverFiniteFaceSelectedIncidentFaces {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (e : Sym2 (ParafermionicCoverBoxVertex n)) :
    Finset (ParafermionicCoverFiniteFaceTopIndex n) :=
  (parafermionicCoverFiniteFaceIncidentFaces e).filter fun i => i ∈ S

section

variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) (e : Sym2 (ParafermionicCoverBoxVertex n))


theorem parafermionicCoverFiniteFaceSelectedIncidentFaces_card_le_two  :
    (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card ≤ 2 := by
  
  apply le_trans (Finset.card_le_card (Finset.filter_subset _ _))
  exact parafermionicCoverFiniteFaceIncidentFaces_card_le_two e

theorem parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_odd
     :
    e ∈ (parafermionicCoverFiniteFaceSetBoundaryGraph S).edgeSet ↔
      (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card % 2 = 1 := by
  classical
  let F : ParafermionicCoverFiniteFaceTopIndex n →
      SimpleGraph (ParafermionicCoverBoxVertex n) :=
    fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2
  
  have hcount : S.toList.countP (fun i => decide (e ∈ (F i).edgeSet)) =
      (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card := by
    have hcount' : (S.filter fun i => e ∈ (F i).edgeSet).card =
        S.toList.countP  fun i => e ∈ (F i).edgeSet  := by
      simpa using  List.Nodup.card_eq_countP S.nodup_toList 
    rw [← hcount']
    apply congrArg Finset.card
    ext i
    simp [parafermionicCoverFiniteFaceSelectedIncidentFaces,
      parafermionicCoverFiniteFaceIncidentFaces, F, and_comm]
  change e ∈ (faceSymmDiffList F S.toList).edgeSet ↔ _
  rw [ faceSymmDiffList_edge_iff_countP_mod F S.toList e , hcount]

theorem parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
     :
    e ∈ (parafermionicCoverFiniteFaceSetBoundaryGraph S).edgeSet ↔
      (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card = 1 := by
  grind [parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_odd,
    parafermionicCoverFiniteFaceSelectedIncidentFaces_card_le_two]

end

end PottsDiscontinuity.TorusTopology.Planar.Medial
