import RequestProject.ClassicalCellAttachmentMaps
import RequestProject.Tac


/-! Partition an arbitrary disk family and attach its two parts successively.
The homeomorphism is constructed directly from both quotient universal maps. -/

noncomputable section
bwd

namespace FiniteChains.RelativeAttachment
open scoped Topology Classical

variable {X J E : Type} [TopologicalSpace X]
  [NormedAddCommGroup E]
  (r : BoundaryFamily J E → X) (p : J → Prop)

def partitionFirstAttaching : BoundaryFamily {j : J // p j} E → X :=
  fun a => r ⟨a.1.val, a.2⟩

def partitionRestAttaching : BoundaryFamily {j : J // ¬p j} E →
    DiskAttachment (partitionFirstAttaching r p) :=
  fun a => old _ _
    (r ⟨a.1.val, a.2⟩)

abbrev PartitionAttachment := DiskAttachment (partitionRestAttaching r p)

def partitionDiskForget (s : J → Prop) :
    C(DiskFamily {j : J // s j} E, DiskFamily J E) where
  toFun d := ⟨d.1.val, d.2⟩
  continuous_toFun := continuous_sigma (fun j =>
    continuous_sigmaMk (σ := fun _ : J => ClosedUnitBall E) (i := j.val))

def partitionFirstInto :
    C(DiskAttachment (partitionFirstAttaching r p), DiskAttachment r) :=
  desc _ _
    ⟨old r _, old_continuous _ _⟩
    ((⟨cell r _, cell_continuous _ _⟩ : C(DiskFamily J E, _)).comp
      (partitionDiskForget p))
    (fun a => (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
      _).symm)

def partitionFlatten : C(PartitionAttachment r p, DiskAttachment r) :=
  desc _ _
    (partitionFirstInto r p)
    ((⟨cell r _, cell_continuous _ _⟩ : C(DiskFamily J E, _)).comp
      (partitionDiskForget _))
    (fun a => (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
      _).symm)


@[simp] theorem partitionFlatten_firstCell d :
    partitionFlatten r p
      (old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
        (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) d)) =
      cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩ := by
  change partitionFirstInto r p
    (cell _ _ d) = _
  unfold partitionFirstInto
  rw [desc_cell]
  rfl

@[simp] theorem partitionFlatten_restCell d :
    partitionFlatten r p
      (cell (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E) d) =
      cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩ := by
  unfold partitionFlatten
  rw [desc_cell]
  rfl

def partitionCellMap : C(DiskFamily J E, PartitionAttachment r p) where
  toFun d := if h : p d.1 then
    old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
      (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E)
        ⟨⟨d.1, h⟩, d.2⟩)
    else cell (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
      ⟨⟨d.1, h⟩, d.2⟩
  continuous_toFun := by
    apply continuous_sigma
    intro j
    by_cases hj : p j
    · simp [dif_pos hj]
      exact (old_continuous _ _).comp ((cell_continuous _ _).comp
        (continuous_sigmaMk (σ := fun _ : {j : J // p j} => ClosedUnitBall E) (i := ⟨j, hj⟩)))
    · simp [dif_neg hj]
      exact (cell_continuous _ _).comp
        (continuous_sigmaMk (σ := fun _ : {j : J // ¬p j} => ClosedUnitBall E) (i := ⟨j, hj⟩))

theorem partitionCellMap_boundary a :
    old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
      (old (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) (r a)) =
      partitionCellMap r p (boundaryFamilyInclusion J E a) := by
  cases' a with j a
  by_cases hj : p j
  · simp [partitionCellMap, ContinuousMap.coe_mk, boundaryFamilyInclusion, dif_pos hj]
    exact congrArg _
      (cell_boundary (partitionFirstAttaching r p) _
        (boundaryFamilyInclusion_isClosedEmbedding _ E).injective
        ⟨⟨j, hj⟩, a⟩).symm
  · simp [partitionCellMap, ContinuousMap.coe_mk, boundaryFamilyInclusion, dif_neg hj]
    exact (cell_boundary (partitionRestAttaching r p) _
      (boundaryFamilyInclusion_isClosedEmbedding _ E).injective
      ⟨⟨j, hj⟩, a⟩).symm

def partitionRegroup : C(DiskAttachment r, PartitionAttachment r p) :=
  desc r _
    ((⟨old _ _,
      old_continuous _ _⟩ : C(DiskAttachment (partitionFirstAttaching r p), _)).comp
        ⟨old _ _,
          old_continuous _ _⟩)
    _ (partitionCellMap_boundary r p)


@[simp] theorem partitionRegroup_firstCell d :
    partitionRegroup r p (cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩) =
      old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
        (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) d) := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp [partitionCellMap, ContinuousMap.coe_mk, dif_pos d.1.property]

@[simp] theorem partitionRegroup_restCell d :
    partitionRegroup r p (cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩) =
      cell (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E) d := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp [partitionCellMap, ContinuousMap.coe_mk, dif_neg d.1.property]

/-- Regrouping preserves each disk point and every old point, with the
original quotient topologies on both sides. -/
def diskAttachmentPartitionHomeomorph : DiskAttachment r ≃ₜ PartitionAttachment r p where
  toFun := partitionRegroup r p
  invFun := partitionFlatten r p
  left_inv z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective r (boundaryFamilyInclusion J E) z
    cases w with
    | inl x => rfl
    | inr d =>
        by_cases hd : p d.1
        · exact (congrArg (partitionFlatten r p)
            (partitionRegroup_firstCell r p ⟨⟨d.1, hd⟩, d.2⟩)).trans
            (partitionFlatten_firstCell r p ⟨⟨d.1, hd⟩, d.2⟩)
        · exact (congrArg (partitionFlatten r p)
            (partitionRegroup_restCell r p ⟨⟨d.1, hd⟩, d.2⟩)).trans
            (partitionFlatten_restCell r p ⟨⟨d.1, hd⟩, d.2⟩)
  right_inv z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective (partitionRestAttaching r p)
      (boundaryFamilyInclusion {j // ¬p j} E) z
    cases w with
    | inl y =>
        obtain ⟨w, rfl⟩ := quotientMap_surjective (partitionFirstAttaching r p)
          (boundaryFamilyInclusion {j // p j} E) y
        cases w with
        | inl x => rfl
        | inr d => exact (congrArg (partitionRegroup r p)
            (partitionFlatten_firstCell r p d)).trans (partitionRegroup_firstCell r p d)
    | inr d => exact (congrArg (partitionRegroup r p)
        (partitionFlatten_restCell r p d)).trans (partitionRegroup_restCell r p d)
  continuous_toFun := (partitionRegroup r p).continuous
  continuous_invFun := (partitionFlatten r p).continuous

theorem partitionRestAttaching_continuous (hr : Continuous r) :
    Continuous (partitionRestAttaching r p) := by
  apply (old_continuous _ _).comp
  simp_all
