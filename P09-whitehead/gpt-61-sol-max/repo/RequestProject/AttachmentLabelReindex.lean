import Mathlib.Tactic

import RequestProject.HomeomorphContinuousMap
import RequestProject.AttachmentDiagramHomeomorph
import RequestProject.ClassicalCellAttachmentMaps

/-! Relabel a family of actual disks without changing its parameters.
The base points and individual characteristic-disk points are retained
by explicit formulas. -/

noncomputable section
namespace FiniteChains.RelativeAttachment


variable {J K X E : Type u} [TopologicalSpace X]
  [NormedAddCommGroup E]

def sigmaLabelHomeomorph {Y : Type u} [TopologicalSpace Y] (e : J ≃ K) :
    (Σ _ : J, Y) ≃ₜ (Σ _ : K, Y) where
  toFun z := ⟨e z.1, z.2⟩
  invFun z := ⟨e.symm z.1, z.2⟩
  left_inv := by grind
  right_inv := by grind
  continuous_toFun := continuous_sigma (fun j =>
    continuous_sigmaMk (σ := fun _ : K => Y) (i := e j))
  continuous_invFun := continuous_sigma (fun k =>
    continuous_sigmaMk (σ := fun _ : J => Y) (i := e.symm k))

variable (r : C(BoundaryFamily J E, X))
  (e : J ≃ K)
def reindexedDiskAttaching    := r.comp (sigmaLabelHomeomorph e).symm.toContinuousMap

def diskAttachmentReindexHomeomorph    :=
  attachmentDiagramHomeomorph r (boundaryFamilyInclusion J E)
    (reindexedDiskAttaching r e) (boundaryFamilyInclusion K E)
    (sigmaLabelHomeomorph (Y := UnitBoundary E) e).toEquiv
    (Homeomorph.refl X) (sigmaLabelHomeomorph (Y := ClosedUnitBall E) e)
    (fun a => by
      solve_by_elim [symm, Homeomorph.symm_apply_apply])
    (fun _ => rfl)
    (boundaryFamilyInclusion_isClosedEmbedding K E).injective
    (boundaryFamilyInclusion_isClosedEmbedding J E).injective



@[simp] theorem diskAttachmentReindexHomeomorph_cell
      (d : DiskFamily J E) :
    diskAttachmentReindexHomeomorph r e (cell r (boundaryFamilyInclusion J E) d) =
      cell (reindexedDiskAttaching r e) (boundaryFamilyInclusion K E) ⟨e d.1, d.2⟩ :=
  attachmentDiagramHomeomorph_cell ..

end FiniteChains.RelativeAttachment
