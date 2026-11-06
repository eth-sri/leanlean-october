/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetVertexIncidence
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceVertexIncidenceBound

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

section
variable (f : ParafermionicCoverVertex)
/-- The four literal lifted vertices of a raw face, labeled counterclockwise
from its southwest corner and retaining the cover sheet. -/
def parafermionicCoverFaceCorner  : Fin 4 →
    ParafermionicCoverVertex
  | ⟨0, _⟩ => f
  | ⟨1, _⟩ => parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2
  | ⟨2, _⟩ => parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2
  | ⟨3, _⟩ => parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2

@[simp] theorem parafermionicCoverFaceCorner_zero  :
    parafermionicCoverFaceCorner f 0 = f := rfl

@[simp] theorem parafermionicCoverFaceCorner_one  :
    parafermionicCoverFaceCorner f 1 =
      parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2 := rfl

@[simp] theorem parafermionicCoverFaceCorner_two  :
    parafermionicCoverFaceCorner f 2 =
      parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2 := rfl

@[simp] theorem parafermionicCoverFaceCorner_three  :
    parafermionicCoverFaceCorner f 3 =
      parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2 := rfl

theorem parafermionicCoverFaceCorner_injective_label  :
    Function.Injective (parafermionicCoverFaceCorner f) := by
  intro c d h
  have hx := congrArg (fun z : ParafermionicCoverVertex => z.1.1) h
  have hy := congrArg (fun z : ParafermionicCoverVertex => z.1.2) h
  fin_cases c <;> fin_cases d <;>
    simp [parafermionicCoverFaceCorner, parafermionicCoverFaceRightLift_formula,
      parafermionicCoverFaceRightUpLift_formula,
      parafermionicCoverFaceRightUpLeftLift_formula] at hx hy ⊢
end

theorem parafermionicCoverFaceCorner_injective_face (c : Fin 4) :
    Function.Injective (fun f : ParafermionicCoverVertex =>
      parafermionicCoverFaceCorner f c) := by
  fin_cases c
  · tauto
  · exact parafermionicCoverFaceRightCorner_injective
  · exact parafermionicCoverFaceRightUpCorner_injective
  · exact parafermionicCoverFaceRightUpLeftCorner_injective

section
variable {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n)
include i
theorem parafermionicCoverFiniteFaceBoundaryGraph_vertex_incident_iff_faceCorner
    (v : ParafermionicCoverBoxVertex n) :
    (∃ w, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).Adj v w) ↔
      ∃ c : Fin 4, parafermionicCoverFaceCorner i.1 c = v.1 := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_vertex_incident_iff_fourCorners]
  constructor
  · rintro (h0 | h1 | h2 | h3)
    · exact ⟨0, by simp_all⟩
    · exact ⟨1, by simp_all⟩
    · exact ⟨2, by simp_all⟩
    · exact ⟨3, by simp_all⟩
  · rintro ⟨c, hc⟩
    fin_cases c <;> simp_all

theorem parafermionicCoverFiniteFaceCorner_mem_box (c : Fin 4) :
    parafermionicCoverFaceCorner i.1 c ∈ parafermionicCoverBoxVertices n := by
  fin_cases c
  · exact (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2
      (e := (i.1, parafermionicCoverFaceRightLift i.1.1.1 i.1.1.2 i.1.2)) (by
        simp [parafermionicCoverFiniteFaceDarts])).1
  · exact (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2
      (e := (i.1, parafermionicCoverFaceRightLift i.1.1.1 i.1.1.2 i.1.2)) (by
        simp [parafermionicCoverFiniteFaceDarts])).2
  · exact (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n i.1 i.2).1
  · exact (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n i.1 i.2).2
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
