module

public import RequestProject.DiskPresentationExtension

@[expose] public section

noncomputable section
namespace FiniteChains.RelativeAttachment.DiskPresentationExtension
open ClassicalGraphModel
open scoped Classical

variable {A B J K : Type} (f : A ↪ B) (c : J ↪ K)
    (r : C(BoundaryFamily J (Fin 2 → ℝ), Rose A))
    (s : C(BoundaryFamily K (Fin 2 → ℝ), Rose B))
    (h : ∀ z, diskRoseMap f (r z) = s ⟨c z.1, z.2⟩)

def sourceIntoExtension : C(DiskAttachment r, DiskAttachment (twoAttaching f c r s)) :=
  (DiskAttachment.oldMap (twoAttaching f c r s)).comp (DiskAttachment.oldMap (oneAttaching f r))

def relatorDiskIntoExtension :
    C(DiskFamily K (Fin 2 → ℝ), DiskAttachment (twoAttaching f c r s)) :=
  ContinuousMap.sigma fun k => if hk : k ∈ Set.range c then
    (sourceIntoExtension f c r s).comp
      (DiskAttachment.cellAt r (Classical.choose hk))
    else DiskAttachment.cellAt (twoAttaching f c r s) ⟨k, hk⟩

def targetToExtension : C(DiskAttachment s, DiskAttachment (twoAttaching f c r s)) :=
  desc s (boundaryFamilyInclusion K _)
    ((DiskAttachment.oldMap (twoAttaching f c r s)).comp (roseIntoOne f r))
    (relatorDiskIntoExtension f c r s) (by
      rintro ⟨k, a⟩
      simp only [relatorDiskIntoExtension, ContinuousMap.sigma_apply, ContinuousMap.comp_apply,
        boundaryFamilyInclusion]
      change old (twoAttaching f c r s) _ (roseIntoOne f r (s ⟨k, a⟩)) = _
      split_ifs with hk
      · have hj  := Classical.choose_spec hk
        have hs : s ⟨k, a⟩ = diskRoseMap f (r ⟨Classical.choose hk, a⟩) := by
          rw [h ⟨Classical.choose hk, a⟩, hj]
        rw [hs, roseIntoOne_map]
        exact congrArg (sourceIntoExtension f c r s)
          (diskCell_boundary r ⟨Classical.choose hk, a⟩).symm
      · exact (diskCell_boundary (twoAttaching f c r s) ⟨⟨k, hk⟩, a⟩).symm)

@[simp] theorem targetToExtension_old (x : Rose B) :
    targetToExtension f c r s h (old s (boundaryFamilyInclusion K _) x) =
      old (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _)
        (roseIntoOne f r x) := rfl

theorem targetToExtension_cell_image (j : J) (d : ClosedUnitBall (Fin 2 → ℝ)) :
    targetToExtension f c r s h (cell s (boundaryFamilyInclusion K _) ⟨c j, d⟩) =
      sourceIntoExtension f c r s (cell r (boundaryFamilyInclusion J _) ⟨j, d⟩) := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  have hk : c j ∈ Set.range c := ⟨j, rfl⟩
  have hj  := c.injective (Classical.choose_spec hk)
  simp only [relatorDiskIntoExtension, ContinuousMap.sigma_apply, dite_eq_left hk, hj]
  rfl

theorem targetToExtension_cell_new (k : NewRelators c) (d : ClosedUnitBall (Fin 2 → ℝ)) :
    targetToExtension f c r s h (cell s (boundaryFamilyInclusion K _) ⟨k.val, d⟩) =
      cell (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _) ⟨k, d⟩ := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp only [relatorDiskIntoExtension, ContinuousMap.sigma_apply, dite_eq_right k.property]
  rfl

theorem targetToExtension_source (x : DiskAttachment r) :
    targetToExtension f c r s h (sourceMap f c r s h x) = sourceIntoExtension f c r s x := by
  induction x using attachment_induction with
  | onOld x =>
      rw [sourceMap_old, targetToExtension_old, roseIntoOne_map]
      rfl
  | onCell d =>
      rw [sourceMap_cell, targetToExtension_cell_image]

theorem extensionToTarget_source (x : DiskAttachment r) :
    extensionToTarget f c r s h (sourceIntoExtension f c r s x) = sourceMap f c r s h x := rfl

theorem extensionToTarget_inverse (x : DiskAttachment s) :
    extensionToTarget f c r s h (targetToExtension f c r s h x) = x := by
  induction x using attachment_induction with
  | onOld x =>
      rw [targetToExtension_old, extensionToTarget_old, oneToTarget_rose]
  | onCell d =>
      rcases d with ⟨k, d⟩
      by_cases hk : k ∈ Set.range c
      · obtain ⟨j, rfl⟩ := hk
        rw [targetToExtension_cell_image, extensionToTarget_source, sourceMap_cell]
      · rw [targetToExtension_cell_new f c r s h ⟨k, hk⟩ d, extensionToTarget_cell]

theorem targetToExtension_inverse (x : DiskAttachment (twoAttaching f c r s)) :
    targetToExtension f c r s h (extensionToTarget f c r s h x) = x := by
  induction x using attachment_induction with
  | onOld x =>
      induction x using attachment_induction with
      | onOld x =>
          change targetToExtension f c r s h
            (extensionToTarget f c r s h (sourceIntoExtension f c r s x)) = _
          rw [extensionToTarget_source, targetToExtension_source]
          rfl
      | onCell d =>
          rw [extensionToTarget_old, oneToTarget_cell, targetToExtension_old,
            roseIntoOne_cell_new]
  | onCell d =>
      rw [extensionToTarget_cell, targetToExtension_cell_new]

def extensionHomeomorph : DiskAttachment (twoAttaching f c r s) ≃ₜ DiskAttachment s where
  toFun := extensionToTarget f c r s h
  invFun := targetToExtension f c r s h
  left_inv := targetToExtension_inverse f c r s h
  right_inv := extensionToTarget_inverse f c r s h
  continuous_toFun := (extensionToTarget f c r s h).continuous
  continuous_invFun := (targetToExtension f c r s h).continuous


def extensionModel : Whitehead.DiskExtensionModel (DiskAttachment r) (DiskAttachment s) where
  oneCells := NewGenerators f
  twoCells := NewRelators c
  oneAttaching := oneAttaching f r
  twoAttaching := twoAttaching f c r s
  comparison := (extensionHomeomorph f c r s h).toHomotopyEquiv


end FiniteChains.RelativeAttachment.DiskPresentationExtension
