module


public import RequestProject.ConeAdjRealizationAttachment
public import RequestProject.OrderNerveLowerCone
public import RequestProject.AttachmentDiagramHomeomorph
public import RequestProject.ClassicalCellAttachmentMaps

@[expose] public section

/-! Replace the actual cone pieces by disks and their actual strict
boundaries by spheres, preserving the old inclusion. Circle geometry is
provided separately, one finite link at a time; the collection of cones
need not be finite. -/

noncomputable section

namespace FiniteChains.Comb
open scoped Topology
open RelativeAttachment

variable {P J : Type} [PartialOrder P] (S : J → P → Prop)
  (C : J → Type) [∀ j, PartialOrder (C j)] [∀ j, Fintype (C j)] [∀ j, Nonempty (C j)]
  (e : ∀ j, C j ≃o StrictBelow (ConeAdj.apex (S := S) j))
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  (b : ∀ j, orderNerveRealization (C j) ≃ₜ UnitBoundary E)

variable (j : J)

def coneAdjLinkOrderIso :=
  (e j).trans (coneAdjBoundaryOrderIso S j).symm

def coneAdjLinkRealizationHomeomorph :=
  orderNerveRealizationOrderIso (coneAdjLinkOrderIso S C e j)

def coneAdjSphereHomeomorph :=
  (coneAdjLinkRealizationHomeomorph S C e j).symm.trans (b j)

def coneAdjBallHomeomorph :=
  lowerConeBallHomeomorph _ (e j) (b j)

omit [∀ j, Fintype _] [∀ j, Nonempty _] in
theorem coneAdjLinkRealization_boundary (x : orderNerveRealization (C j)) :
    orderNerveRealizationMap Subtype.val
        (fun _ _ h => h) (coneAdjLinkRealizationHomeomorph S C e j x) =
      orderNerveRealizationMap _
        (lowerConeBoundary _ (e j)).monotone x := by
  solve_by_elim [orderNerveRealizationMap_comp]

theorem coneAdjBallHomeomorph_boundary
    (x : orderNerveRealization (ConeAdjBoundary S j)) :
    coneAdjBallHomeomorph S C e b j
        (orderNerveRealizationMap Subtype.val (fun _ _ h => h) x) =
      unitBoundaryInclusion E (coneAdjSphereHomeomorph S C e b j x) := by
  have h := lowerConeBallHomeomorph_boundary _ (e j) (b j)
    ((coneAdjLinkRealizationHomeomorph S C e j).symm x)
  erw [← coneAdjLinkRealization_boundary S C e j, Homeomorph.apply_symm_apply] at h <;> assumption

def coneAdjSphereFamilyHomeomorph :=
  sigmaFiberHomeomorph (coneAdjSphereHomeomorph S C e b)

def coneAdjBallFamilyHomeomorph :=
  sigmaFiberHomeomorph (coneAdjBallHomeomorph S C e b)

def coneAdjDiskAttaching :=
  (coneAdjRealizationAttaching S).comp (coneAdjSphereFamilyHomeomorph S C e b).symm.toContinuousMap

omit [∀ j, Fintype _] [∀ j, Nonempty _] [NormedSpace ℝ E] [ProperSpace E] in
theorem coneAdjDiskAttaching_link (j : J) (x : orderNerveRealization (C j)) :
    coneAdjDiskAttaching S C e b ⟨j, b j x⟩ =
      coneAdjRealizationAttaching S ⟨j, coneAdjLinkRealizationHomeomorph S C e j x⟩ := by
  have hs : coneAdjSphereFamilyHomeomorph S C e b
      ⟨j, coneAdjLinkRealizationHomeomorph S C e j x⟩ = ⟨j, b j x⟩ := by
    change (⟨j, b j _⟩ : BoundaryFamily J E) = _
    simp
  change coneAdjRealizationAttaching S
    _ = _
  erw [← hs, Homeomorph.symm_apply_apply]

theorem coneAdjRealizationBoundary_injective : Function.Injective (coneAdjRealizationBoundary S) := by
  rintro ⟨j, x⟩ ⟨k, y⟩ h
  have hk : j = k := congrArg Sigma.fst h
  subst k
  exact congrArg _ (orderNerveRealizationMap_injective
    Subtype.val (fun _ _ h => h)
    Subtype.val_injective (eq_of_heq (Sigma.mk.inj h).2))

def coneAdjAttachmentDiskHomeomorph :=
  attachmentDiagramHomeomorph
    (coneAdjRealizationAttaching S) _
    (coneAdjDiskAttaching S C e b) _
    (coneAdjSphereFamilyHomeomorph S C e b).toEquiv (Homeomorph.refl _)
    (coneAdjBallFamilyHomeomorph S C e b)
    (fun a => by
      change coneAdjRealizationAttaching S a = coneAdjRealizationAttaching S
        ((coneAdjSphereFamilyHomeomorph S C e b).symm
          (coneAdjSphereFamilyHomeomorph S C e b a))
      simp)
    (fun a => by
      rcases a with ⟨j, x⟩
      exact congrArg (Sigma.mk j) (coneAdjBallHomeomorph_boundary S C e b j x))
    (boundaryFamilyInclusion_isClosedEmbedding J E).injective
    (coneAdjRealizationBoundary_injective S)

/-- The realization is a genuine family of disks attached to its old part. -/
def coneAdjRealizationDiskHomeomorph :=
  (coneAdjRealizationAttachmentHomeomorph S).symm.trans
    (coneAdjAttachmentDiskHomeomorph S C e b)

@[simp] theorem coneAdjRealizationDiskHomeomorph_old
    (x : orderNerveRealization (ConeAdjBase S)) :
    coneAdjRealizationDiskHomeomorph S C e b (coneAdjRealizationOld S x) =
      old _ _ x := by
  erw [← coneAdjRealizationAttachmentHomeomorph_old]
  change coneAdjAttachmentDiskHomeomorph S C e b
    _ = _
  erw [Homeomorph.symm_apply_apply]
  exact attachmentDiagramHomeomorph_old ..

@[simp] theorem coneAdjRealizationDiskHomeomorph_cell
    (z : Σ j, orderNerveRealization (ConeAdjDisk S j)) :
    coneAdjRealizationDiskHomeomorph S C e b (coneAdjRealizationCell S z) =
      cell _ _
        (coneAdjBallFamilyHomeomorph S C e b z) := by
  erw [← coneAdjRealizationAttachmentHomeomorph_cell]
  change coneAdjAttachmentDiskHomeomorph S C e b
    _ = _
  erw [Homeomorph.symm_apply_apply]
  exact attachmentDiagramHomeomorph_cell ..

end FiniteChains.Comb
