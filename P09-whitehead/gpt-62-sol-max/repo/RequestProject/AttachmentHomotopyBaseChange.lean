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

def attachmentBaseMapEquivOfHomotopicId (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (h : C(P, P))
    (H : ContinuousMap.Homotopy (ContinuousMap.id P) h) :
    ContinuousMap.HomotopyEquiv (Space a Subtype.val) (Space (h ∘ a) Subtype.val) := by
  let Hatt  := H.compContinuousMap a
  let C := (attachingHomotopyEquiv S hS hext hfull a (h.comp a) Hatt).symm
  let F := attachmentBaseMap a Subtype.val Subtype.val_injective h
  let L := attachingDiskExtension S hext a (h.comp a) Hatt
  let HOld : C(I × P, Space a Subtype.val) :=
    ⟨fun tp => old a Subtype.val (H tp), (old_continuous _ _).comp H.continuous⟩
  have hcompat : ∀ t b, HOld (t, a b) = L (t, b.val) := by
    intro t b
    exact (attachingDiskExtension_side S hext a (h.comp a) Hatt t b).symm
  have HT : (ContinuousMap.id (Space a Subtype.val)).Homotopy (C.toFun.comp F) := by
    refine attachmentHomotopy a Subtype.val HOld L hcompat
      ⟨fun p => congrArg (old a Subtype.val) (H.apply_zero p), ?_⟩
      ⟨fun p => congrArg (old a Subtype.val) (H.apply_one p), ?_⟩
    · exact attachingDiskExtension_zero S hext a (h.comp a) Hatt
    · intro d
      change L (1, d) = attachingBackwardMap S hext a (h.comp a) Hatt (F (cell a Subtype.val d))
      rw [attachmentBaseMap_cell]
      exact (attachingBackwardMap_cell S hext a (h.comp a) Hatt d).symm
  exact ContinuousMap.HomotopyEquiv.ofHomotopicSection C F ⟨HT.symm⟩


/-- Change of the base by an actual homotopy equivalence induces an actual
homotopy equivalence on the attached spaces. Its forward map is precisely
the universal pushout map extending the original base map and disk maps. -/
def attachmentBaseChangeHomotopyEquiv (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (e : ContinuousMap.HomotopyEquiv P K) :
    ContinuousMap.HomotopyEquiv (Space a Subtype.val) (Space (e.toFun ∘ a) Subtype.val) := by
  let f := attachmentBaseMap a Subtype.val Subtype.val_injective e.toFun
  let g := attachmentBaseMap (e.toFun ∘ a) Subtype.val Subtype.val_injective e.invFun
  let h := attachmentBaseMap (e.invFun ∘ e.toFun ∘ a) Subtype.val
    Subtype.val_injective e.toFun
  let E := attachmentBaseMapEquivOfHomotopicId S hS hext hfull a
    (e.invFun.comp e.toFun) (Classical.choice e.left_inv).symm
  let D := attachmentBaseMapEquivOfHomotopicId S hS hext hfull (e.toFun.comp a)
    (e.toFun.comp e.invFun) (Classical.choice e.right_inv).symm
  have hE  :=
    (attachmentBaseMap_comp a Subtype.val Subtype.val_injective e.toFun e.invFun).symm
  have hD  :=
    (attachmentBaseMap_comp (e.toFun ∘ a) Subtype.val
      Subtype.val_injective e.invFun e.toFun).symm
  exact ContinuousMap.HomotopyEquiv.twoOfSixLeft f g h E hE D hD

@[simp] theorem attachmentBaseChangeHomotopyEquiv_toFun (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (e : ContinuousMap.HomotopyEquiv P K) :
    (attachmentBaseChangeHomotopyEquiv S hS hext hfull a e).toFun =
      attachmentBaseMap a Subtype.val Subtype.val_injective e.toFun := rfl


end FiniteChains.RelativeAttachment
