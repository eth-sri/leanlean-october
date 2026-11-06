import RequestProject.AttachingHomotopyEquiv
import RequestProject.HomotopyEquivCancellation


/-! Homotopy invariance of actual cell attachments under change of their
base. Both required homotopy extension properties are supplied for disks
by the explicit ball constructions. No equivalence of the pushout is
assumed in the conclusion's construction. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {D P K : Type u} [TopologicalSpace D] [TopologicalSpace P] [TopologicalSpace K]

def attachmentBaseMapEquivOfHomotopicId S (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) h
    (H : ContinuousMap.Homotopy (ContinuousMap.id P) h) :
    ContinuousMap.HomotopyEquiv (Space a Subtype.val) (Space (h ∘ a) Subtype.val) := by
  let Hatt : a.Homotopy (h.comp a) := H.compContinuousMap a
  let C := (attachingHomotopyEquiv S hS hext hfull a _ Hatt).symm
  let F := attachmentBaseMap a Subtype.val Subtype.val_injective h
  let L := attachingDiskExtension S hext a _ Hatt
  let HOld : C(I × P, Space a Subtype.val) :=
    ⟨fun tp => old a Subtype.val (H tp), (old_continuous _ _).comp H.continuous⟩
  have hcompat : ∀ t b, HOld (t, a b) = L (t, b.val) := by
    intro t b
    exact (attachingDiskExtension_side S hext a _ Hatt t b).symm
  let T := attachmentHomotopyPasting a Subtype.val HOld L hcompat
  have HT : ContinuousMap.Homotopy (ContinuousMap.id _)
      (C.toFun.comp F) := {
    toContinuousMap := T
    map_zero_left := by
      intro z
      obtain ⟨w, rfl⟩ := quotientMap_surjective a Subtype.val z
      cases w with
      | inl p => exact congrArg (old a Subtype.val) (H.apply_zero p)
      | inr d =>
        exact (attachmentHomotopyPasting_cell a Subtype.val HOld L hcompat 0 d).trans
          (attachingDiskExtension_zero S hext a _ Hatt d)
    map_one_left := by
      intro z
      obtain ⟨w, rfl⟩ := quotientMap_surjective a Subtype.val z
      cases w with
      | inl p =>
        change old a Subtype.val (H (1, p)) = old a Subtype.val (h p)
        simp
      | inr d =>
        change T (1, cell a Subtype.val d) =
          attachingBackwardMap S hext a _ Hatt (F (cell a Subtype.val d))
        rw [attachmentHomotopyPasting_cell, attachmentBaseMap_cell]
        exact (attachingBackwardMap_cell S hext a _ Hatt d).symm }
  exact C.ofHomotopicSection F ⟨HT.symm⟩


/-- Change of the base by an actual homotopy equivalence induces an actual
homotopy equivalence on the attached spaces. Its forward map is precisely
the universal pushout map extending the original base map and disk maps. -/
def attachmentBaseChangeHomotopyEquiv S (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (e : ContinuousMap.HomotopyEquiv P K) :
    ContinuousMap.HomotopyEquiv (Space a Subtype.val) (Space (e.toFun ∘ a) Subtype.val) := by
  let f := attachmentBaseMap a Subtype.val Subtype.val_injective e.toFun
  let g := attachmentBaseMap (e.toFun ∘ a) Subtype.val Subtype.val_injective e.invFun
  let h := attachmentBaseMap (e.invFun ∘ e.toFun ∘ a) Subtype.val
    Subtype.val_injective e.toFun
  let E := attachmentBaseMapEquivOfHomotopicId S hS hext hfull a
    _ (Classical.choice e.left_inv).symm
  let D := attachmentBaseMapEquivOfHomotopicId S hS hext hfull (e.toFun.comp a)
    _ (Classical.choice e.right_inv).symm
  have hE :=
    (attachmentBaseMap_comp a Subtype.val Subtype.val_injective e.toFun e.invFun).symm
  have hD :=
    (attachmentBaseMap_comp (e.toFun ∘ a) Subtype.val
      Subtype.val_injective e.invFun e.toFun).symm
  exact ContinuousMap.HomotopyEquiv.twoOfSixLeft f g h E hE D hD

@[simp] theorem attachmentBaseChangeHomotopyEquiv_toFun S hS
    hext
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    a (e : ContinuousMap.HomotopyEquiv P K) :
    (attachmentBaseChangeHomotopyEquiv S hS hext hfull a e).toFun =
      attachmentBaseMap a Subtype.val Subtype.val_injective e.toFun := rfl
