import Mathlib.Tactic

import RequestProject.PresClassicalDiskComparison
import RequestProject.RelatorCircleBoundaryNaturality
import RequestProject.DiskRoseMaps

/-! The actual attaching maps and disk-model maps commute with literal
presentation-word embeddings. Circle-coordinate compatibility is proved
by the explicit traversal, rather than supplied as an extra hypothesis. -/

noncomputable section
namespace FiniteChains.PresModel.PresWordEmbedding
open Comb RelativeAttachment ClassicalGraphModel


variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v) (hw : ∀ j, w j ≠ []) (hv : ∀ k, v k ≠ [])

variable (z : BoundaryFamily J (Fin 2 → ℝ))
theorem actualPresWordAttaching_natural  :
    orderNerveRealizationMap h.roseMap h.roseMap.monotone (actualPresWordAttaching w hw z) =
      actualPresWordAttaching v hv ⟨h.cell z.1, z.2⟩ := by
  classical grind [FiniteChains.PresModel.actualPresWordAttaching_apply, FiniteChains.PresModel.PresWordEmbedding.relatorCircleBoundaryHomeomorph_symm_natural, FiniteChains.PresModel.PresWordEmbedding.presCircleWordMap_natural, presCircleBoundaryHomeomorph]

theorem classicalPresWordAttaching_natural  :
    diskRoseMap h.gen (classicalPresWordAttaching w hw z) =
      classicalPresWordAttaching v hv ⟨h.cell z.1, z.2⟩ := by
  dsimp [FiniteChains.PresModel.classicalPresWordAttaching]
  rw [← orderRoseRealizationHomeomorph_natural h, h.actualPresWordAttaching_natural hw hv z]

def orderRoseMapContinuous  :=
  (orderNerveRealizationMap h.roseMap h.roseMap.monotone).hom

def wordDiskCellMap : C(DiskFamily J (Fin 2 → ℝ), ActualPresWordDisks v hv) :=
  (⟨RelativeAttachment.cell (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)),
    cell_continuous _ _⟩ : C(DiskFamily K (Fin 2 → ℝ), _)).comp
      ⟨fun d => ⟨h.cell d.1, d.2⟩, continuous_sigma (fun j => continuous_sigmaMk
          (σ := fun _ : K => ClosedUnitBall (Fin 2 → ℝ)) (i := h.cell j))⟩

def wordDiskMap  :=
  desc (actualPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ))
    ((⟨old (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)),
      old_continuous _ _⟩ : C(orderNerveRealization (PresModel.Rose B), _)).comp
        h.orderRoseMapContinuous)
    (h.wordDiskCellMap hv)
    (fun a => by
      change old (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        (orderNerveRealizationMap h.roseMap h.roseMap.monotone
        (actualPresWordAttaching w hw a)) =
          RelativeAttachment.cell _ _ (boundaryFamilyInclusion K (Fin 2 → ℝ) ⟨h.cell a.1, a.2⟩)
      rw [cell_boundary _ _ (boundaryFamilyInclusion_isClosedEmbedding K (Fin 2 → ℝ)).injective,
        h.actualPresWordAttaching_natural hw hv])

@[simp] theorem wordDiskMap_old (x : orderNerveRealization (PresModel.Rose A)) :
    h.wordDiskMap hw hv (old (actualPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ)) x) =
      old (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        (orderNerveRealizationMap h.roseMap h.roseMap.monotone x) := rfl

variable (d : DiskFamily J (Fin 2 → ℝ))
@[simp] theorem wordDiskMap_cell  :
    h.wordDiskMap hw hv (RelativeAttachment.cell (actualPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ)) d) =
      RelativeAttachment.cell (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        ⟨h.cell d.1, d.2⟩ := desc_cell ..

def classicalWordDiskMap  :=
  desc (classicalPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ))
    ((⟨old (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)),
      old_continuous _ _⟩ : C(ClassicalGraphModel.Rose B, _)).comp (diskRoseMap h.gen))
    ((⟨RelativeAttachment.cell (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)),
      cell_continuous _ _⟩ : C(DiskFamily K (Fin 2 → ℝ), _)).comp
        ⟨fun d => ⟨h.cell d.1, d.2⟩, continuous_sigma (fun j => continuous_sigmaMk
          (σ := fun _ : K => ClosedUnitBall (Fin 2 → ℝ)) (i := h.cell j))⟩)
    (fun a => by
      change old (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        (diskRoseMap h.gen (classicalPresWordAttaching w hw a)) =
        RelativeAttachment.cell _ _ (boundaryFamilyInclusion K (Fin 2 → ℝ) ⟨h.cell a.1, a.2⟩)
      rw [cell_boundary _ _ (boundaryFamilyInclusion_isClosedEmbedding K (Fin 2 → ℝ)).injective,
        h.classicalPresWordAttaching_natural hw hv])

@[simp] theorem classicalWordDiskMap_old (x : ClassicalGraphModel.Rose A) :
    h.classicalWordDiskMap hw hv
      (old (classicalPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ)) x) =
      old (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        (diskRoseMap h.gen x) := rfl

@[simp] theorem classicalWordDiskMap_cell  :
    h.classicalWordDiskMap hw hv
      (RelativeAttachment.cell (classicalPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ)) d) =
      RelativeAttachment.cell (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        ⟨h.cell d.1, d.2⟩ := desc_cell ..

end FiniteChains.PresModel.PresWordEmbedding
