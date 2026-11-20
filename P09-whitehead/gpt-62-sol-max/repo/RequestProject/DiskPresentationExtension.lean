module

public import RequestProject.DiskRoseMaps
public import RequestProject.DiskFamilyMap
public import RequestProject.ClassicalCWModelSequenceTransfer

@[expose] public section

/-! A literal inclusion of disk presentations is a relative one-cell
attachment followed by a relative two-cell attachment. The cell sets are
the actual complements of the two injective label maps. All characteristic
disk parameters are preserved, including on the old presentation. -/

noncomputable section
namespace FiniteChains.RelativeAttachment.DiskPresentationExtension
open ClassicalGraphModel
open scoped Classical

variable {A B J K : Type} (f : A ↪ B) (c : J ↪ K)
    (r : C(BoundaryFamily J (Fin 2 → ℝ), Rose A))
    (s : C(BoundaryFamily K (Fin 2 → ℝ), Rose B))
    (h : ∀ z, diskRoseMap f (r z) = s ⟨c z.1, z.2⟩)

abbrev NewGenerators := {b : B // b ∉ Set.range f}
abbrev NewRelators := {k : K // k ∉ Set.range c}

def sourceMap : C(DiskAttachment r, DiskAttachment s) :=
  diskFamilyMap r s (diskRoseMap f) c (fun j a => h ⟨j, a⟩)

@[simp] theorem sourceMap_old (x : Rose A) :
    sourceMap f c r s h (old r (boundaryFamilyInclusion J _) x) =
      old s (boundaryFamilyInclusion K _) (diskRoseMap f x) := rfl

@[simp] theorem sourceMap_cell (d : DiskFamily J (Fin 2 → ℝ)) :
    sourceMap f c r s h (cell r (boundaryFamilyInclusion J _) d) =
      cell s (boundaryFamilyInclusion K _) ⟨c d.1, d.2⟩ := diskFamilyMap_cell ..

def oneAttaching : C(BoundaryFamily (NewGenerators f) (Fin 1 → ℝ), DiskAttachment r) :=
  ContinuousMap.const _ (old r (boundaryFamilyInclusion J _) (roseVertex A))

def roseDiskIntoOne : C(DiskFamily B (Fin 1 → ℝ), DiskAttachment (oneAttaching f r)) :=
  ContinuousMap.sigma fun b => if hb : b ∈ Set.range f then
    (DiskAttachment.oldMap (oneAttaching f r)).comp ((DiskAttachment.oldMap r).comp
      (DiskAttachment.cellAt (roseAttaching A) (Classical.choose hb)))
    else DiskAttachment.cellAt (oneAttaching f r) ⟨b, hb⟩

def roseIntoOne : C(Rose B, DiskAttachment (oneAttaching f r)) :=
  desc (roseAttaching B) (boundaryFamilyInclusion B _)
    (ContinuousMap.const _ (old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _)
      (old r (boundaryFamilyInclusion J _) (roseVertex A))))
    (roseDiskIntoOne f r) (by
      rintro ⟨b, x⟩
      simp only [roseDiskIntoOne, ContinuousMap.sigma_apply]
      split_ifs with hb
      · exact congrArg (fun y => old (oneAttaching f r) _ (old r _ y))
          (diskCell_boundary (roseAttaching A) ⟨Classical.choose hb, x⟩).symm
      · exact (diskCell_boundary (oneAttaching f r) ⟨⟨b, hb⟩, x⟩).symm)



theorem roseIntoOne_cell_image (a : A) (d : ClosedUnitBall (Fin 1 → ℝ)) :
    roseIntoOne f r (cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨f a, d⟩) =
      old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _)
        (old r (boundaryFamilyInclusion J _)
          (cell (roseAttaching A) (boundaryFamilyInclusion A _) ⟨a, d⟩)) := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  have hb : f a ∈ Set.range f := ⟨a, rfl⟩
  have ha  := f.injective (Classical.choose_spec hb)
  simp only [roseDiskIntoOne, ContinuousMap.sigma_apply, dite_eq_left hb, ha]
  rfl

theorem roseIntoOne_cell_new (b : NewGenerators f) (d : ClosedUnitBall (Fin 1 → ℝ)) :
    roseIntoOne f r (cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨b.val, d⟩) =
      cell (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _) ⟨b, d⟩ := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp only [roseDiskIntoOne, ContinuousMap.sigma_apply, dite_eq_right b.property]
  rfl

theorem roseIntoOne_map (x : Rose A) : roseIntoOne f r (diskRoseMap f x) =
    old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _)
      (old r (boundaryFamilyInclusion J _) x) := by
  induction x using attachment_induction with
  | onOld a => cases a; rfl
  | onCell d =>
      rw [diskRoseMap_cell, roseIntoOne_cell_image]

def twoAttaching : C(BoundaryFamily (NewRelators c) (Fin 2 → ℝ),
    DiskAttachment (oneAttaching f r)) :=
  (roseIntoOne f r).comp (s.comp (reindexFamily Subtype.val))

def oneToTarget : C(DiskAttachment (oneAttaching f r), DiskAttachment s) :=
  desc (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _)
    (sourceMap f c r s h)
    ((DiskAttachment.oldMap s).comp
      ((DiskAttachment.cellMap (roseAttaching B)).comp (reindexFamily Subtype.val)))
    (fun z => by
      change old s _ (diskRoseMap f (roseVertex A)) = old s _ (cell _ _ _)
      rw [diskRoseMap_vertex]
      exact congrArg (old s _) (diskCell_boundary (roseAttaching B) ⟨z.1.val, z.2⟩).symm)

@[simp] theorem oneToTarget_old (x : DiskAttachment r) :
    oneToTarget f c r s h (old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _) x) =
      sourceMap f c r s h x := rfl

@[simp] theorem oneToTarget_cell (d : DiskFamily (NewGenerators f) (Fin 1 → ℝ)) :
    oneToTarget f c r s h (cell (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _) d) =
      old s (boundaryFamilyInclusion K _)
        (cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨d.1.val, d.2⟩) := desc_cell ..

theorem oneToTarget_rose (x : Rose B) :
    oneToTarget f c r s h (roseIntoOne f r x) = old s (boundaryFamilyInclusion K _) x := by
  induction x using attachment_induction with
  | onOld a => cases a; rfl
  | onCell d =>
      rcases d with ⟨b, d⟩
      by_cases hb : b ∈ Set.range f
      · obtain ⟨a, rfl⟩ := hb
        rw [roseIntoOne_cell_image, oneToTarget_old, sourceMap_old, diskRoseMap_cell]
      · rw [roseIntoOne_cell_new f r ⟨b, hb⟩ d, oneToTarget_cell]

def extensionToTarget : C(DiskAttachment (twoAttaching f c r s), DiskAttachment s) :=
  desc (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _)
    (oneToTarget f c r s h)
    ((DiskAttachment.cellMap s).comp (reindexFamily Subtype.val))
    (fun z => (oneToTarget_rose f c r s h (s ⟨z.1.val, z.2⟩)).trans
      (diskCell_boundary s ⟨z.1.val, z.2⟩).symm)

@[simp] theorem extensionToTarget_old (x : DiskAttachment (oneAttaching f r)) :
    extensionToTarget f c r s h (old (twoAttaching f c r s)
      (boundaryFamilyInclusion (NewRelators c) _) x) = oneToTarget f c r s h x := rfl

@[simp] theorem extensionToTarget_cell (d : DiskFamily (NewRelators c) (Fin 2 → ℝ)) :
    extensionToTarget f c r s h (cell (twoAttaching f c r s)
      (boundaryFamilyInclusion (NewRelators c) _) d) =
      cell s (boundaryFamilyInclusion K _) ⟨d.1.val, d.2⟩ := desc_cell ..

end FiniteChains.RelativeAttachment.DiskPresentationExtension
