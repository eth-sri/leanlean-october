module

public import RequestProject.AttachingHomotopyEquiv
public import RequestProject.HomotopyEquivCancellation

@[expose] public section

/-! Homotopy invariance of actual cell attachments under change of their
base. Both required homotopy extension properties are supplied for disks
by the explicit ball constructions. No equivalence of the pushout is
assumed in the conclusion's construction. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {D P K : Type u} [TopologicalSpace D] [TopologicalSpace P] [TopologicalSpace K]

variable (S : Set D)
    (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P))

variable (h : C(P, P)) (H : ContinuousMap.Homotopy (ContinuousMap.id P) h)

def attachmentBaseMapEquivOfHomotopicId :
    ContinuousMap.HomotopyEquiv (Space a Subtype.val) (Space (h ∘ a) Subtype.val) := by
  let Hatt := H.compContinuousMap a
  let C := (attachingHomotopyEquiv S hS hext hfull a _ Hatt).symm
  let F := attachmentBaseMap a Subtype.val Subtype.val_injective h
  let L := attachingDiskExtension S hext a _ Hatt
  let HOld : C(I × P, Space a Subtype.val) :=
    ⟨fun tp => old a Subtype.val _, (old_continuous _ _).comp H.continuous⟩
  have hcompat : ∀ t b, HOld (t, a b) = L (t, b.val) := by
    intro t b
    exact (attachingDiskExtension_side S hext a _ Hatt t b).symm
  let T := attachmentHomotopyPasting a Subtype.val HOld L hcompat
  have HT : ContinuousMap.Homotopy (ContinuousMap.id (Space a Subtype.val))
      (C.toFun.comp F) := {
    toContinuousMap := T
    map_zero_left := by
      intro z
      obtain ⟨w, rfl⟩ := quotientMap_surjective a Subtype.val z
      cases w with
      | inl p => exact congrArg _ (H.apply_zero p)
      | inr d =>
        exact (attachmentHomotopyPasting_cell a Subtype.val HOld L hcompat 0 d).trans
          (attachingDiskExtension_zero S hext a (h.comp a) Hatt d)
    map_one_left := by
      intro z
      obtain ⟨w, rfl⟩ := quotientMap_surjective a Subtype.val z
      cases w with
      | inl p =>
        exact congrArg _ (H.apply_one p)
      | inr d =>
        change T (1, cell a Subtype.val d) =
          attachingBackwardMap S hext a _ Hatt (F (cell a Subtype.val d))
        rw [attachmentHomotopyPasting_cell, attachmentBaseMap_cell]
        exact (attachingBackwardMap_cell S hext a _ Hatt d).symm }
  exact ContinuousMap.HomotopyEquiv.ofHomotopicSection C F ⟨HT.symm⟩

@[simp] theorem attachmentBaseMapEquivOfHomotopicId_toFun :
    (attachmentBaseMapEquivOfHomotopicId S hS hext hfull a h H).toFun =
      attachmentBaseMap a Subtype.val Subtype.val_injective h := rfl

variable (e : ContinuousMap.HomotopyEquiv P K)

/-- Change of the base by an actual homotopy equivalence induces an actual
homotopy equivalence on the attached spaces. Its forward map is precisely
the universal pushout map extending the original base map and disk maps. -/
def attachmentBaseChangeHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (Space a Subtype.val) (Space (e.toFun ∘ a) Subtype.val) := by
  let h := attachmentBaseMap (e.invFun ∘ e.toFun ∘ a) Subtype.val
    Subtype.val_injective e.toFun
  let E := attachmentBaseMapEquivOfHomotopicId S hS hext hfull a
    _ (Classical.choice e.left_inv).symm
  let D := attachmentBaseMapEquivOfHomotopicId S hS hext hfull (e.toFun.comp a)
    _ (Classical.choice e.right_inv).symm
  have hD :=
    (attachmentBaseMap_comp (e.toFun ∘ a) Subtype.val
      Subtype.val_injective e.invFun e.toFun).symm
  exact ContinuousMap.HomotopyEquiv.twoOfSixLeft _ _ h E (attachmentBaseMap_comp a Subtype.val Subtype.val_injective e.toFun e.invFun).symm D hD

@[simp] theorem attachmentBaseChangeHomotopyEquiv_toFun :
    (attachmentBaseChangeHomotopyEquiv S hS hext hfull a e).toFun =
      attachmentBaseMap a Subtype.val Subtype.val_injective e.toFun := rfl

@[simp] theorem attachmentBaseChangeHomotopyEquiv_old (p : P) :
    attachmentBaseChangeHomotopyEquiv S hS hext hfull a e (old a Subtype.val p) =
      old _ Subtype.val (e p) := rfl

end FiniteChains.RelativeAttachment
