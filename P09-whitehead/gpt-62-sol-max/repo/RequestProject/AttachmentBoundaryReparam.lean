module

public import RequestProject.AttachmentDiagramHomeomorph

@[expose] public section

/-! Reparametrizing the boundary changes neither the literal old points
nor the attached disk points, and gives a genuine homeomorphism. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped Classical

universe u
variable {A D P : Type u} [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace P]

def attachmentBoundaryReparam (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) :
    Space a i ≃ₜ Space (a ∘ b.symm) Subtype.val :=
  attachmentDiagramHomeomorph a i (a ∘ b.symm) Subtype.val b.toEquiv
    (.refl _) (.refl _) (fun x => by simp) (fun x => (hb x).symm) Subtype.val_injective hi

@[simp] theorem attachmentBoundaryReparam_cell (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) (d : D) :
    attachmentBoundaryReparam a i hi S b hb (cell a i d) =
      cell (a ∘ b.symm) Subtype.val d := attachmentDiagramHomeomorph_cell ..

@[simp] theorem attachmentBoundaryReparam_symm_cell (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) (d : D) :
    (attachmentBoundaryReparam a i hi S b hb).symm (cell (a ∘ b.symm) Subtype.val d) =
      cell a i d := (Homeomorph.symm_apply_eq _).2 (attachmentBoundaryReparam_cell ..).symm

end FiniteChains.RelativeAttachment
