import RequestProject.HomeomorphContinuousMap
import RequestProject.NaturalDiskAttachingExtensions


/-! Attaching-map change with natural forward map. The inverse proof uses
the established full-cylinder backtrack homotopy with the explicit ball
extensions supplied here. Unverified source. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped Classical Topology unitInterval ContinuousMap
variable {J E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

def naturalDiskReparam (r : C(BoundaryFamily J E, X)) :=
  attachmentBoundaryReparam r _
    (boundaryFamilyInclusion_isClosedEmbedding J E).injective
    _ (diskFamilyBoundaryHomeomorph J E) (by simp)

def naturalSubspaceExtension (r₀ r₁ : C(BoundaryFamily J E, X)) (H : r₀.Homotopy r₁) :=
  (naturalDiskReparam r₀).toContinuousMap.comp (naturalDiskExtension r₀ r₁ H)

theorem naturalSubspaceExtension_zero (r₀ r₁ : C(BoundaryFamily J E, X))
    H d :
    naturalSubspaceExtension r₀ r₁ H (0, d) =
      cell (r₀ ∘ (diskFamilyBoundaryHomeomorph J E).symm) Subtype.val d := by
  change naturalDiskReparam r₀ (naturalDiskExtension r₀ r₁ H (0, d)) = _
  rw [naturalDiskExtension_zero]
  exact attachmentBoundaryReparam_cell ..

theorem naturalSubspaceExtension_side (r₀ r₁ : C(BoundaryFamily J E, X))
    H t a :
    naturalSubspaceExtension r₀ r₁ H (t, a.val) =
      old (r₀ ∘ (diskFamilyBoundaryHomeomorph J E).symm) Subtype.val
        ((H.compContinuousMap (diskFamilyBoundaryHomeomorph J E).symm.toContinuousMap) (t, a)) := by
  let b := diskFamilyBoundaryHomeomorph J E
  have ha : boundaryFamilyInclusion J E (b.symm a) = a.val :=
    congrArg Subtype.val (b.apply_symm_apply a)
  change naturalDiskReparam r₀ (naturalDiskExtension r₀ r₁ H (t, a.val)) = _
  rw [← ha, naturalDiskExtension_boundary]
  rfl

def naturalDiskAttachingEquiv (r₀ r₁ : C(BoundaryFamily J E, X))
    (H : r₀.Homotopy r₁) : DiskAttachment r₀ ≃ₕ DiskAttachment r₁ :=
  let b := diskFamilyBoundaryHomeomorph J E
  let e := attachingHomotopyEquivOfExtensions _
    _ _
    (H.compContinuousMap b.symm.toContinuousMap)
    _ _
    (naturalSubspaceExtension_zero r₀ r₁ H) (naturalSubspaceExtension_zero r₁ r₀ H.symm)
    (naturalSubspaceExtension_side r₀ r₁ H) (naturalSubspaceExtension_side r₁ r₀ H.symm)
    (diskFamilyBoundarySet_isClosed J E) (diskFamilyFullCylinder_hasHomotopyExtension E J)
  ((naturalDiskReparam r₀).toHomotopyEquiv.trans e).trans
    (naturalDiskReparam r₁).symm.toHomotopyEquiv

theorem naturalDiskAttachingEquiv_toFun (r₀ r₁ : C(BoundaryFamily J E, X))
    H :
    (naturalDiskAttachingEquiv r₀ r₁ H).toFun = naturalDiskBackward r₁ r₀ H.symm := by
  apply hom_ext r₀ _
  · intro x
    rfl
  · intro d
    let b := diskFamilyBoundaryHomeomorph J E
    change (naturalDiskReparam r₁).symm
      (chosenAttachingForward _
        _ _
        (H.compContinuousMap b.symm.toContinuousMap)
        _
        (naturalSubspaceExtension_side r₁ r₀ H.symm)
        (naturalDiskReparam r₀ (cell r₀ _ d))) = _
    rw [show naturalDiskReparam r₀ (cell r₀ _ d) =
      cell _ Subtype.val d
        from attachmentBoundaryReparam_cell ..]
    change (naturalDiskReparam r₁).symm (desc _ _ _ _ _ (cell _ _ d)) = _
    rw [desc_cell]
    change (naturalDiskReparam r₁).symm
      (naturalDiskReparam r₁ (naturalDiskExtension r₁ r₀ H.symm (1, d))) = _
    simp


theorem naturalDiskAttachingEquiv_natural
    {K Y} [TopologicalSpace Y]
    r₀ r₁ H
    (s₀ s₁ : C(BoundaryFamily K E, Y)) G
    (f : C(X, Y)) (i : J → K)
    h₀
    h₁
    (hH : ∀ t j a, f (H (t, ⟨j, a⟩)) = G (t, ⟨i j, a⟩)) :
    (diskFamilyMap r₁ s₁ f i h₁).comp (naturalDiskAttachingEquiv r₀ r₁ H).toFun =
      (naturalDiskAttachingEquiv s₀ s₁ G).toFun.comp (diskFamilyMap r₀ s₀ f i h₀) := by
  rw [naturalDiskAttachingEquiv_toFun, naturalDiskAttachingEquiv_toFun]
  exact naturalDiskBackward_natural r₁ r₀ H.symm s₁ s₀ G.symm f i h₁ h₀
    (by tauto)
