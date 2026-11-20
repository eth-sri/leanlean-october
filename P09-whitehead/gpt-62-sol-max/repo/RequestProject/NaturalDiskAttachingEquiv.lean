module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.NaturalDiskAttachingExtensions

@[expose] public section

/-! Attaching-map change with natural forward map. The inverse proof uses
the established full-cylinder backtrack homotopy with the explicit ball
extensions supplied here. Unverified source. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped Classical Topology unitInterval ContinuousMap
variable {J E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

def naturalSubspaceExtension (r₀ r₁ : C(BoundaryFamily J E, X)) (H : r₀.Homotopy r₁) :
    C(I × DiskFamily J E,
      Space (r₀ ∘ (diskFamilyBoundaryHomeomorph J E).symm) Subtype.val) :=
  (diskAttachmentReparam r₀).toContinuousMap.comp (naturalDiskExtension r₀ r₁ H)

theorem naturalSubspaceExtension_zero (r₀ r₁ : C(BoundaryFamily J E, X))
    (H : r₀.Homotopy r₁) (d : DiskFamily J E) :
    naturalSubspaceExtension r₀ r₁ H (0, d) =
      cell (r₀ ∘ (diskFamilyBoundaryHomeomorph J E).symm) Subtype.val d := by
  change diskAttachmentReparam r₀ (naturalDiskExtension r₀ r₁ H (0, d)) = _
  rw [naturalDiskExtension_zero]
  exact attachmentBoundaryReparam_cell ..

theorem naturalSubspaceExtension_side (r₀ r₁ : C(BoundaryFamily J E, X))
    (H : r₀.Homotopy r₁) (t : I) (a : diskFamilyBoundarySet J E) :
    naturalSubspaceExtension r₀ r₁ H (t, a.val) =
      old (r₀ ∘ (diskFamilyBoundaryHomeomorph J E).symm) Subtype.val
        ((H.compContinuousMap (diskFamilyBoundaryHomeomorph J E).symm.toContinuousMap) (t, a)) := by
  let b := diskFamilyBoundaryHomeomorph J E
  have ha : boundaryFamilyInclusion J E (b.symm a) = a.val :=
    congrArg Subtype.val (b.apply_symm_apply a)
  change diskAttachmentReparam r₀ (naturalDiskExtension r₀ r₁ H (t, a.val)) = _
  rw [← ha, naturalDiskExtension_boundary]
  rfl

def naturalDiskAttachingEquiv (r₀ r₁ : C(BoundaryFamily J E, X))
    (H : r₀.Homotopy r₁) : DiskAttachment r₀ ≃ₕ DiskAttachment r₁ :=
  let b := diskFamilyBoundaryHomeomorph J E
  let e := attachingHomotopyEquivOfExtensions (diskFamilyBoundarySet J E)
    (r₀.comp b.symm.toContinuousMap) (r₁.comp b.symm.toContinuousMap)
    (H.compContinuousMap b.symm.toContinuousMap)
    (naturalSubspaceExtension r₀ r₁ H) (naturalSubspaceExtension r₁ r₀ H.symm)
    (naturalSubspaceExtension_zero r₀ r₁ H) (naturalSubspaceExtension_zero r₁ r₀ H.symm)
    (naturalSubspaceExtension_side r₀ r₁ H) (naturalSubspaceExtension_side r₁ r₀ H.symm)
    (diskFamilyBoundarySet_isClosed J E) (diskFamilyFullCylinder_hasHomotopyExtension E J)
  ((diskAttachmentReparam r₀).toHomotopyEquiv.trans e).trans
    (diskAttachmentReparam r₁).symm.toHomotopyEquiv

theorem naturalDiskAttachingEquiv_toFun (r₀ r₁ : C(BoundaryFamily J E, X))
    (H : r₀.Homotopy r₁) :
    (naturalDiskAttachingEquiv r₀ r₁ H).toFun = naturalDiskBackward r₁ r₀ H.symm := by
  apply hom_ext r₀ (boundaryFamilyInclusion J E)
  · intro x
    rfl
  · intro d
    let b := diskFamilyBoundaryHomeomorph J E
    change (diskAttachmentReparam r₁).symm
      (chosenAttachingForward (diskFamilyBoundarySet J E)
        (r₀.comp b.symm.toContinuousMap) (r₁.comp b.symm.toContinuousMap)
        (H.compContinuousMap b.symm.toContinuousMap)
        (naturalSubspaceExtension r₁ r₀ H.symm)
        (naturalSubspaceExtension_side r₁ r₀ H.symm)
        (diskAttachmentReparam r₀ (cell r₀ (boundaryFamilyInclusion J E) d))) = _
    rw [show diskAttachmentReparam r₀ (cell r₀ (boundaryFamilyInclusion J E) d) =
      cell (r₀ ∘ (diskFamilyBoundaryHomeomorph J E).symm) Subtype.val d
        from attachmentBoundaryReparam_cell ..]
    change (diskAttachmentReparam r₁).symm (desc _ _ _ _ _ (cell _ _ d)) = _
    rw [desc_cell]
    change (diskAttachmentReparam r₁).symm
      (diskAttachmentReparam r₁ (naturalDiskExtension r₁ r₀ H.symm (1, d))) = _
    rw [Homeomorph.symm_apply_apply, naturalDiskBackward_cell]


theorem naturalDiskAttachingEquiv_natural
    {K Y : Type} [TopologicalSpace Y]
    (r₀ r₁ : C(BoundaryFamily J E, X)) (H : r₀.Homotopy r₁)
    (s₀ s₁ : C(BoundaryFamily K E, Y)) (G : s₀.Homotopy s₁)
    (f : C(X, Y)) (i : J → K)
    (h₀ : ∀ j a, f (r₀ ⟨j, a⟩) = s₀ ⟨i j, a⟩)
    (h₁ : ∀ j a, f (r₁ ⟨j, a⟩) = s₁ ⟨i j, a⟩)
    (hH : ∀ t j a, f (H (t, ⟨j, a⟩)) = G (t, ⟨i j, a⟩)) :
    (diskFamilyMap r₁ s₁ f i h₁).comp (naturalDiskAttachingEquiv r₀ r₁ H).toFun =
      (naturalDiskAttachingEquiv s₀ s₁ G).toFun.comp (diskFamilyMap r₀ s₀ f i h₀) := by
  rw [naturalDiskAttachingEquiv_toFun, naturalDiskAttachingEquiv_toFun]
  solve_by_elim [naturalDiskBackward_natural]

end FiniteChains.RelativeAttachment
