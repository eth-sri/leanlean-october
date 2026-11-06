import Mathlib.Tactic

import RequestProject.HomeomorphContinuousMap
import RequestProject.ClassicalCellAttachmentMaps
import RequestProject.SigmaCylinderHomotopyExtension
import RequestProject.AttachmentBoundaryReparam
import RequestProject.AttachmentHomotopyBaseChange
import RequestProject.TopologicalPi2HomotopyTransport

/-! Homotopy invariance for arbitrary families of actual disk attachments.
All extension inputs are discharged by the explicit ball/cylinder maps.
The forward map retains the disk labels and is the given map on old points. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeAttachment


variable (J E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

def diskFamilyBoundarySet  :=
  SigmaSubspace (fun _ : J => {d : ClosedUnitBall E | ‖d.val‖ = 1})

section
omit [NormedSpace ℝ E]
theorem diskFamilyBoundarySet_isClosed : IsClosed (diskFamilyBoundarySet J E) :=
  sigmaSubspace_isClosed _ (fun _ =>
    isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const)

abbrev boundaryFamilyInclusion_range_eq  :=
  Set.ext fun (d : FiniteChains.RelativeAttachment.DiskFamily J E) =>
    FiniteChains.RelativeAttachment.boundaryFamilyInclusion_range J E d
end

def diskFamilyBoundaryHomeomorph : BoundaryFamily J E ≃ₜ diskFamilyBoundarySet J E :=
  (boundaryFamilyInclusion_isClosedEmbedding J E).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (boundaryFamilyInclusion_range_eq J E))



variable {J E}
variable {P K : Type u} [TopologicalSpace P] [TopologicalSpace K]

  (r : C(BoundaryFamily J E, P))
  (e : ContinuousMap.HomotopyEquiv P K)
/-- The actual homotopy equivalence after attaching an arbitrary family
of disks along a homotopy equivalence of the old spaces. -/
def diskAttachmentBaseChangeHomotopyEquiv 
     :
    ContinuousMap.HomotopyEquiv (DiskAttachment r) (DiskAttachment (e.toFun ∘ r)) := by
  let S := diskFamilyBoundarySet J E
  let b := diskFamilyBoundaryHomeomorph J E
  have hb : ∀ a, (b a).val = boundaryFamilyInclusion J E a := fun _ => rfl
  have hi := (boundaryFamilyInclusion_isClosedEmbedding J E).injective
  let R₀ := attachmentBoundaryReparam r (boundaryFamilyInclusion J E) hi S b hb
  let R₁ := attachmentBoundaryReparam (e.toFun ∘ r) (boundaryFamilyInclusion J E) hi S b hb
  let a  := r.comp b.symm.toContinuousMap
  let H := attachmentBaseChangeHomotopyEquiv S (diskFamilyBoundarySet_isClosed J E)
    (diskFamilySubspace_hasHomotopyExtension E J)
    (diskFamilyFullCylinder_hasHomotopyExtension E J) a e
  exact (R₀.toHomotopyEquiv.trans H).trans R₁.symm.toHomotopyEquiv

@[simp] theorem diskAttachmentBaseChangeHomotopyEquiv_old
      (p : P) :
    diskAttachmentBaseChangeHomotopyEquiv r e (old r (boundaryFamilyInclusion J E) p) =
      old (e.toFun ∘ r) (boundaryFamilyInclusion J E) (e p) := rfl

@[simp] theorem diskAttachmentBaseChangeHomotopyEquiv_cell
     
    (d : DiskFamily J E) :
    diskAttachmentBaseChangeHomotopyEquiv r e (cell r (boundaryFamilyInclusion J E) d) =
      cell (e.toFun ∘ r) (boundaryFamilyInclusion J E) d := by
  simp only [diskAttachmentBaseChangeHomotopyEquiv, ContinuousMap.HomotopyEquiv.trans, ContinuousMap.comp_apply, ContinuousMap.coe_coe, Homeomorph.toHomotopyEquiv, attachmentBoundaryReparam_cell]
  let R := attachmentBoundaryReparam (e.toFun ∘ r) (boundaryFamilyInclusion J E)
    (boundaryFamilyInclusion_isClosedEmbedding J E).injective
    (diskFamilyBoundarySet J E) (diskFamilyBoundaryHomeomorph J E) (fun _ => rfl)
  exact (congrArg R.symm
    (attachmentBaseMap_cell (r.comp (diskFamilyBoundaryHomeomorph J E).symm.toContinuousMap)
      Subtype.val Subtype.val_injective e.toFun d)).trans
    (attachmentBoundaryReparam_symm_cell (e.toFun ∘ r) (boundaryFamilyInclusion J E)
      (boundaryFamilyInclusion_isClosedEmbedding J E).injective
      (diskFamilyBoundarySet J E) (diskFamilyBoundaryHomeomorph J E) (fun _ => rfl) d)

/-- Moving all attaching maps through specified homotopies gives an actual
equivalence which is the identity on the old space. This permits cellular
representatives to be chosen after changing the base. -/
def diskAttachingHomotopyEquiv (r₀ r₁ : C(BoundaryFamily J E, P))
    (H : r₀.Homotopy r₁) :
    ContinuousMap.HomotopyEquiv (DiskAttachment r₀) (DiskAttachment r₁) := by
  let S := diskFamilyBoundarySet J E
  let b := diskFamilyBoundaryHomeomorph J E
  have hb : ∀ a, (b a).val = boundaryFamilyInclusion J E a := fun _ => rfl
  have hi := (boundaryFamilyInclusion_isClosedEmbedding J E).injective
  let R₀ := attachmentBoundaryReparam r₀ (boundaryFamilyInclusion J E) hi S b hb
  let R₁ := attachmentBoundaryReparam r₁ (boundaryFamilyInclusion J E) hi S b hb
  let E' := attachingHomotopyEquiv S (diskFamilyBoundarySet_isClosed J E)
    (diskFamilySubspace_hasHomotopyExtension E J)
    (diskFamilyFullCylinder_hasHomotopyExtension E J)
    (r₀.comp b.symm.toContinuousMap) (r₁.comp b.symm.toContinuousMap)
    (H.compContinuousMap b.symm.toContinuousMap)
  exact (R₀.toHomotopyEquiv.trans E').trans R₁.symm.toHomotopyEquiv



end FiniteChains.RelativeAttachment





