module

public import RequestProject.ClassicalCellAttachmentMaps

@[expose] public section

/-! Partition an arbitrary disk family and attach its two parts successively.
The homeomorphism is constructed directly from both quotient universal maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeAttachment
open scoped Topology Classical

variable {X J E : Type} [TopologicalSpace X]
  [NormedAddCommGroup E]
  (r : BoundaryFamily J E → X) (p : J → Prop)

def partitionFirstAttaching : BoundaryFamily {j : J // p j} E → X :=
  fun a => r ⟨a.1.val, a.2⟩

def partitionRestAttaching : BoundaryFamily {j : J // ¬p j} E →
    DiskAttachment (partitionFirstAttaching r p) :=
  fun a => old (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E)
    (r ⟨a.1.val, a.2⟩)

abbrev PartitionAttachment := DiskAttachment (partitionRestAttaching r p)

def partitionDiskForget (s : J → Prop) :
    C(DiskFamily {j : J // s j} E, DiskFamily J E) := reindexFamily Subtype.val

def partitionFirstInto :
    C(DiskAttachment (partitionFirstAttaching r p), DiskAttachment r) :=
  desc (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E)
    (DiskAttachment.oldMap r)
    ((DiskAttachment.cellMap r).comp (partitionDiskForget p))
    (fun a => (diskCell_boundary r ⟨a.1.val, a.2⟩).symm)

def partitionFlatten : C(PartitionAttachment r p, DiskAttachment r) :=
  desc (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
    (partitionFirstInto r p)
    ((DiskAttachment.cellMap r).comp (partitionDiskForget (fun j => ¬p j)))
    (fun a => (diskCell_boundary r ⟨a.1.val, a.2⟩).symm)


@[simp] theorem partitionFlatten_firstCell (d : DiskFamily {j // p j} E) :
    partitionFlatten r p
      (old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
        (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) d)) =
      cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩ := by
  change partitionFirstInto r p
    (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) d) = _
  unfold partitionFirstInto
  rw [desc_cell]
  rfl

@[simp] theorem partitionFlatten_restCell (d : DiskFamily {j // ¬p j} E) :
    partitionFlatten r p
      (cell (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E) d) =
      cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩ := by
  unfold partitionFlatten
  rw [desc_cell]
  rfl

def partitionCellMap : C(DiskFamily J E, PartitionAttachment r p) :=
  ContinuousMap.sigma fun j => if h : p j then
    (DiskAttachment.oldMap (partitionRestAttaching r p)).comp
      (DiskAttachment.cellAt (partitionFirstAttaching r p) ⟨j, h⟩)
    else DiskAttachment.cellAt (partitionRestAttaching r p) ⟨j, h⟩

theorem partitionCellMap_boundary (a : BoundaryFamily J E) :
    old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
      (old (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) (r a)) =
      partitionCellMap r p (boundaryFamilyInclusion J E a) := by
  rcases a with ⟨j, a⟩
  by_cases hj : p j
  · simp only [partitionCellMap, ContinuousMap.sigma_apply, boundaryFamilyInclusion, dif_pos hj]
    exact congrArg (old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E))
      (diskCell_boundary (partitionFirstAttaching r p) ⟨⟨j, hj⟩, a⟩).symm
  · simp only [partitionCellMap, ContinuousMap.sigma_apply, boundaryFamilyInclusion, dif_neg hj]
    exact (diskCell_boundary (partitionRestAttaching r p) ⟨⟨j, hj⟩, a⟩).symm

def partitionRegroup : C(DiskAttachment r, PartitionAttachment r p) :=
  desc r (boundaryFamilyInclusion J E)
    ((DiskAttachment.oldMap (partitionRestAttaching r p)).comp
      (DiskAttachment.oldMap (partitionFirstAttaching r p)))
    (partitionCellMap r p) (partitionCellMap_boundary r p)


@[simp] theorem partitionRegroup_firstCell (d : DiskFamily {j // p j} E) :
    partitionRegroup r p (cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩) =
      old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
        (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) d) := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp only [partitionCellMap, ContinuousMap.sigma_apply, dif_pos d.1.property]
  rfl

@[simp] theorem partitionRegroup_restCell (d : DiskFamily {j // ¬p j} E) :
    partitionRegroup r p (cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩) =
      cell (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E) d := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp only [partitionCellMap, ContinuousMap.sigma_apply, dif_neg d.1.property]
  rfl

/-- Regrouping preserves each disk point and every old point, with the
original quotient topologies on both sides. -/
def diskAttachmentPartitionHomeomorph : DiskAttachment r ≃ₜ PartitionAttachment r p where
  toFun := partitionRegroup r p
  invFun := partitionFlatten r p
  left_inv z := by
    induction z using attachment_induction with
    | onOld x => rfl
    | onCell d =>
        by_cases hd : p d.1
        · exact (congrArg (partitionFlatten r p)
            (partitionRegroup_firstCell r p ⟨⟨d.1, hd⟩, d.2⟩)).trans
            (partitionFlatten_firstCell r p ⟨⟨d.1, hd⟩, d.2⟩)
        · exact (congrArg (partitionFlatten r p)
            (partitionRegroup_restCell r p ⟨⟨d.1, hd⟩, d.2⟩)).trans
            (partitionFlatten_restCell r p ⟨⟨d.1, hd⟩, d.2⟩)
  right_inv z := by
    induction z using attachment_induction with
    | onOld y =>
        induction y using attachment_induction with
        | onOld x => rfl
        | onCell d => exact (congrArg (partitionRegroup r p)
            (partitionFlatten_firstCell r p d)).trans (partitionRegroup_firstCell r p d)
    | onCell d => exact (congrArg (partitionRegroup r p)
        (partitionFlatten_restCell r p d)).trans (partitionRegroup_restCell r p d)
  continuous_toFun := (partitionRegroup r p).continuous
  continuous_invFun := (partitionFlatten r p).continuous

theorem partitionRestAttaching_continuous (hr : Continuous r) :
    Continuous (partitionRestAttaching r p) := by
  apply (old_continuous _ _).comp
  simp_all

end FiniteChains.RelativeAttachment
