/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarFiniteTriangularPivotReachability
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFacePivotBypass
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetPivots
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceUnionConnectivity

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

section
variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
/-- The actual selected-face union graph after deleting precisely its selected
top-pivot edges, on the same original box-vertex carrier. -/
noncomputable def parafermionicCoverFiniteFaceSetWithoutPivotsGraph  :
    SimpleGraph (ParafermionicCoverBoxVertex n) :=
  (parafermionicCoverFiniteFaceUnionGraph S).deleteEdges
    (parafermionicCoverFiniteFaceSetPivots S : Set _)

theorem parafermionicCoverFiniteFaceSetWithoutPivotsGraph_reachable_eq
     :
    (parafermionicCoverFiniteFaceSetWithoutPivotsGraph S).Reachable =
      (parafermionicCoverFiniteFaceUnionGraph S).Reachable := by
  let I := {i : ParafermionicCoverFiniteFaceTopIndex n // i ∈ S}
  let U := parafermionicCoverFiniteFaceUnionGraph S
  let F : I → SimpleGraph (ParafermionicCoverBoxVertex n) :=
    fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1.1 i.1.2
  let p : I → Sym2 (ParafermionicCoverBoxVertex n) :=
    fun i => parafermionicCoverFiniteFaceTopPivot n i.1
  let rank : I → ℕ := fun i => parafermionicCoverFiniteFaceTopRank n i.1
  have hsub : ∀ i, F i ≤ U := by
    intro i v w hadj
    exact ⟨i.1, i.2, hadj⟩
  have htri : ∀ i j, p j ∈ (F i).edgeSet → j = i ∨ rank j < rank i := by
    intro i j hj
    have hclass := parafermionicCoverFiniteFacePivot_boundary_classification
      i.1 j.1 (by omega)
    grind
  have halt : ∀ i,
      ((F i).deleteEdges {p i}).Reachable (p i).out.1 (p i).out.2 := by
    intro i
    simpa using parafermionicCoverFiniteFaceTopPivot_bypass i.1
  have hrange : Set.range p =
      (parafermionicCoverFiniteFaceSetPivots S : Set (Sym2 (ParafermionicCoverBoxVertex n))) := by
    ext e
    simp only [Set.mem_range, Finset.mem_coe, parafermionicCoverFiniteFaceSetPivots,
      Finset.mem_image]
    constructor
    · grind
    tauto
  simpa [parafermionicCoverFiniteFaceSetWithoutPivotsGraph, U, hrange] using (finiteTriangularPivotReachability U F p rank hsub htri halt)
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
