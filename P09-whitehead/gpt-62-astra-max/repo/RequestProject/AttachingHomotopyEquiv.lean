module


public import RequestProject.AttachmentBacktrackHomotopy

@[expose] public section

/-! Homotopic attaching maps have homotopy equivalent attachment spaces.
The equivalence is the identity on the literal old summand. The inverse
and both homotopies are constructed using disk and cylinder extension. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {D P : Type u} [TopologicalSpace D] [TopologicalSpace P]

variable (S : Set D)

section

variable (hext : HasHomotopyExtension (Subtype.val : S → D)) (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁)
include hext a₁

theorem exists_attachingDiskExtension :
    ∃ L : C(I × D, Space a₀ Subtype.val),
      (∀ d, L (0, d) = cell a₀ Subtype.val d) ∧
      ∀ t a, L (t, a.val) = old a₀ Subtype.val (H (t, a)) := by
  apply hext _
    ⟨cell a₀ Subtype.val, cell_continuous _ _⟩
    ((⟨old a₀ Subtype.val, old_continuous _ _⟩ : C(P, Space a₀ Subtype.val)).comp
      H.toContinuousMap)
  simp_all [cell_boundary]

def attachingDiskExtension :=
  Classical.choose (exists_attachingDiskExtension S hext a₀ a₁ H)

theorem attachingDiskExtension_zero (d : D) :
    attachingDiskExtension S hext a₀ a₁ H (0, d) = cell a₀ Subtype.val d :=
  by grind [attachingDiskExtension]

theorem attachingDiskExtension_side (t : I) (a : S) :
    attachingDiskExtension S hext a₀ a₁ H (t, a.val) = old a₀ Subtype.val (H (t, a)) :=
  by grind [attachingDiskExtension]

def attachingBackwardMap :=
  desc a₁ Subtype.val ⟨old a₀ Subtype.val, old_continuous _ _⟩
    ((attachingDiskExtension S hext a₀ a₁ H).comp
      ⟨fun d => (1, d), continuous_const.prodMk continuous_id⟩)
    (fun a => by
      simp_all [attachingDiskExtension_side])

@[simp] theorem attachingBackwardMap_old (p : P) :
    attachingBackwardMap S hext a₀ a₁ H (old a₁ Subtype.val p) = old a₀ Subtype.val p := rfl

@[simp] theorem attachingBackwardMap_cell (d : D) :
    attachingBackwardMap S hext a₀ a₁ H (cell a₁ Subtype.val d) =
      attachingDiskExtension S hext a₀ a₁ H (1, d) := by
  unfold attachingBackwardMap
  rw [desc_cell]
  rfl

end

def attachingHomotopyEquiv (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) :
    ContinuousMap.HomotopyEquiv (Space a₀ Subtype.val) (Space a₁ Subtype.val) where
  toFun := attachingBackwardMap S hext a₁ a₀ H.symm
  invFun := attachingBackwardMap S hext a₀ a₁ H
  left_inv := attachingBacktrack_homotopic_id S hS hfull a₀ a₁ H _ _
    (attachingBackwardMap_old S hext a₀ a₁ H)
    (attachingBackwardMap_old S hext a₁ a₀ H.symm)
    _
    _
    (attachingDiskExtension_zero S hext a₀ a₁ H)
    (attachingDiskExtension_zero S hext a₁ a₀ H.symm)
    (attachingDiskExtension_side S hext a₀ a₁ H)
    (attachingDiskExtension_side S hext a₁ a₀ H.symm)
    (attachingBackwardMap_cell S hext a₀ a₁ H)
    (attachingBackwardMap_cell S hext a₁ a₀ H.symm)
  right_inv := by
    apply attachingBacktrack_homotopic_id S hS hfull a₁ a₀ H.symm _ _
      (attachingBackwardMap_old S hext a₁ a₀ H.symm)
      (attachingBackwardMap_old S hext a₀ a₁ H)
      _
      _
      (attachingDiskExtension_zero S hext a₁ a₀ H.symm)
      (attachingDiskExtension_zero S hext a₀ a₁ H)
      (attachingDiskExtension_side S hext a₁ a₀ H.symm) _
      (attachingBackwardMap_cell S hext a₁ a₀ H.symm)
      (attachingBackwardMap_cell S hext a₀ a₁ H)
    simp_all [attachingDiskExtension_side]

end FiniteChains.RelativeAttachment
