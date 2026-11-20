module

public import RequestProject.ExplicitRelativeAttachment

@[expose] public section

/-! Reparametrizing the boundary changes neither the literal old points
nor the attached disk points, and gives a genuine homeomorphism. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped Classical

universe u
variable {A D P : Type u} [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace P]

variable (a : A → P) (i : A → D)

def attachmentBoundaryReparamForward (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) :=
  desc a i ⟨old (a ∘ b.symm) Subtype.val, old_continuous _ _⟩
    ⟨cell (a ∘ b.symm) Subtype.val, cell_continuous _ _⟩ (fun x => by
      change old (a ∘ b.symm) Subtype.val (a x) = cell (a ∘ b.symm) Subtype.val (i x)
      rw [← hb x, cell_boundary _ Subtype.val Subtype.val_injective] <;> simp_all)

variable (hi : Function.Injective i) (S : Set D) (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x)

def attachmentBoundaryReparamBackward :=
  desc (a ∘ b.symm) Subtype.val ⟨old a i, old_continuous _ _⟩
    ⟨cell a i, cell_continuous _ _⟩ (fun x => by
      change old a i (a (b.symm x)) = cell a i x.val
      rw [← ((hb (b.symm x)).symm.trans (congrArg Subtype.val (b.apply_symm_apply x))), cell_boundary a i hi])

def attachmentBoundaryReparam :
    Space a i ≃ₜ Space (a ∘ b.symm) Subtype.val where
  toFun := attachmentBoundaryReparamForward a i S b hb
  invFun := attachmentBoundaryReparamBackward a i hi S b hb
  left_inv z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective a i z
    cases w with
    | inl p => rfl
    | inr d =>
      change desc _ _ _ _ _ (desc _ _ _ _ _ (cell a i d)) = cell a i d
      simp
  right_inv z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective _ Subtype.val z
    cases w with
    | inl p => rfl
    | inr d =>
      change desc _ _ _ _ _ (desc _ _ _ _ _ (cell _ Subtype.val d)) = _
      aesop
  continuous_toFun := (attachmentBoundaryReparamForward a i S b hb).continuous
  continuous_invFun := (attachmentBoundaryReparamBackward a i hi S b hb).continuous

@[simp] theorem attachmentBoundaryReparam_old (p : P) :
    attachmentBoundaryReparam a i hi S b hb (old a i p) =
      old _ Subtype.val p := rfl

@[simp] theorem attachmentBoundaryReparam_cell (d : D) :
    attachmentBoundaryReparam a i hi S b hb (cell a i d) =
      cell _ Subtype.val d := by
  change attachmentBoundaryReparamForward a i S b hb _ = _
  unfold attachmentBoundaryReparamForward
  rw [desc_cell]
  rfl

@[simp] theorem attachmentBoundaryReparam_symm_old (p : P) :
    (attachmentBoundaryReparam a i hi S b hb).symm (old (a ∘ b.symm) Subtype.val p) =
      old a i p := rfl

@[simp] theorem attachmentBoundaryReparam_symm_cell (d : D) :
    (attachmentBoundaryReparam a i hi S b hb).symm (cell (a ∘ b.symm) Subtype.val d) =
      cell a i d := by
  change attachmentBoundaryReparamBackward a i hi S b hb
    _ = _
  unfold attachmentBoundaryReparamBackward
  rw [desc_cell]
  rfl

end FiniteChains.RelativeAttachment
