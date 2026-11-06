/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetEdgeCount

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

/-- The distinct actual top-pivot edges attached to a selected set of actual
retained lifted faces. -/
noncomputable def parafermionicCoverFiniteFaceSetPivots {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))  :=
  S.image (parafermionicCoverFiniteFaceTopPivot n)

section

variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))


theorem parafermionicCoverFiniteFaceSetPivots_card  :
    (parafermionicCoverFiniteFaceSetPivots S).card = S.card := Finset.card_image_of_injective S (parafermionicCoverFiniteFaceTopPivot_injective n)

theorem parafermionicCoverFiniteFaceSetPivots_subset_edgeSupport  :
    parafermionicCoverFiniteFaceSetPivots S ⊆
      parafermionicCoverFiniteFaceSetEdgeSupport S := by
  classical
  intro e he
  rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
  have htop := parafermionicCoverFiniteFaceTopEdgeBox_mem_boundaryGraph i.1 i.2
  have heq : parafermionicCoverFiniteFaceTopEdgeBox i.1 i.2 =
      parafermionicCoverFiniteFaceTopPivot n i := rfl
  
  have hinc : i ∈ parafermionicCoverFiniteFaceIncidentFaces
      (parafermionicCoverFiniteFaceTopPivot n i) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (by
                                                                                                 simpa [heq] using htop)⟩
  
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, ⟨i,  Finset.mem_filter.mpr ⟨hinc, hi⟩ ⟩⟩

theorem parafermionicCoverFiniteFaceSetEdgeSupport_sdiff_pivots_card  :
    (parafermionicCoverFiniteFaceSetEdgeSupport S \ parafermionicCoverFiniteFaceSetPivots S).card +
      S.card = (parafermionicCoverFiniteFaceSetEdgeSupport S).card := by
  
  calc
    _ = (parafermionicCoverFiniteFaceSetEdgeSupport S \ parafermionicCoverFiniteFaceSetPivots S).card +
        (parafermionicCoverFiniteFaceSetPivots S).card := by
          rw [parafermionicCoverFiniteFaceSetPivots_card]
    _ = (parafermionicCoverFiniteFaceSetEdgeSupport S).card :=
      Finset.card_sdiff_add_card_eq_card (parafermionicCoverFiniteFaceSetPivots_subset_edgeSupport S)

end

end PottsDiscontinuity.TorusTopology.Planar.Medial
