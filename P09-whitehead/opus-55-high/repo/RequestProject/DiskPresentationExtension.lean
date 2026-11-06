import RequestProject.DiskRoseMaps
import RequestProject.ClassicalCWModelSequenceTransfer


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
  desc r (boundaryFamilyInclusion J _)
    ((⟨old s _, old_continuous _ _⟩ : C(Rose B, _)).comp
      (diskRoseMap f))
    ⟨fun d => cell s _ ⟨c d.1, d.2⟩,
      continuous_sigma (fun j => (cell_continuous s _).comp
        (continuous_sigmaMk (σ := fun _ : K => ClosedUnitBall (Fin 2 → ℝ)) (i := c j)))⟩
    (fun z => by
      change old s (boundaryFamilyInclusion K (Fin 2 → ℝ)) (diskRoseMap f (r z)) =
        cell s _ ⟨c z.1, unitBoundaryInclusion _ z.2⟩
      rw [h z]
      exact (cell_boundary s _ (boundaryFamilyInclusion_isClosedEmbedding K _).injective
        _).symm)

@[simp] theorem sourceMap_old x :
    sourceMap f c r s h (old r (boundaryFamilyInclusion J _) x) =
      old s (boundaryFamilyInclusion K _) (diskRoseMap f x) := rfl

@[simp] theorem sourceMap_cell d :
    sourceMap f c r s h (cell r (boundaryFamilyInclusion J _) d) =
      cell s (boundaryFamilyInclusion K _) ⟨c d.1, d.2⟩ := desc_cell ..

def oneAttaching : C(BoundaryFamily (NewGenerators f) (Fin 1 → ℝ), DiskAttachment r) :=
  ContinuousMap.const _ (old r _ (roseVertex A))

def roseDiskIntoOne : C(DiskFamily B (Fin 1 → ℝ), DiskAttachment (oneAttaching f r)) where
  toFun d := if hb : d.1 ∈ Set.range f then
    old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _)
      (old r (boundaryFamilyInclusion J _)
        (cell (roseAttaching A) (boundaryFamilyInclusion A _) ⟨Classical.choose hb, d.2⟩))
    else cell (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _) ⟨⟨d.1, hb⟩, d.2⟩
  continuous_toFun := by
    apply continuous_sigma
    intro b
    by_cases hb : b ∈ Set.range f
    · simp only [dif_pos hb]
      exact (old_continuous _ _).comp ((old_continuous _ _).comp
        ((cell_continuous _ _).comp
          (continuous_sigmaMk (σ := fun _ : A => ClosedUnitBall (Fin 1 → ℝ))
            (i := Classical.choose hb))))
    · simp only [dif_neg hb]
      exact (cell_continuous _ _).comp
        (continuous_sigmaMk (σ := fun _ : NewGenerators f => ClosedUnitBall (Fin 1 → ℝ))
          (i := ⟨b, hb⟩))

def roseIntoOne : C(Rose B, DiskAttachment (oneAttaching f r)) :=
  desc (roseAttaching B) (boundaryFamilyInclusion B _)
    (ContinuousMap.const _ (old _ _
      (old r _ (roseVertex A))))
    (roseDiskIntoOne f r) (by
      rintro ⟨b, x⟩
      change _ = if hb : b ∈ Set.range f then _ else _
      split_ifs with hb
      · exact congrArg (fun y => old _ _ (old r _ y))
          (cell_boundary _ _
            (boundaryFamilyInclusion_isClosedEmbedding A _).injective
            ⟨hb.choose, x⟩).symm
      · exact (cell_boundary (oneAttaching f r) _
          (boundaryFamilyInclusion_isClosedEmbedding _ _).injective
          ⟨⟨b, hb⟩, x⟩).symm)


theorem roseIntoOne_cell_image a d :
    roseIntoOne f r (cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨f a, d⟩) =
      old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _)
        (old r (boundaryFamilyInclusion J _)
          (cell (roseAttaching A) (boundaryFamilyInclusion A _) ⟨a, d⟩)) := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  have hb : f a ∈ Set.range f := by simp
  have ha : hb.choose = a := by simp
  simp only [roseDiskIntoOne, ContinuousMap.coe_mk, dif_pos hb, ha]

theorem roseIntoOne_cell_new b d :
    roseIntoOne f r (cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨b.val, d⟩) =
      cell (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _) ⟨b, d⟩ := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp only [roseDiskIntoOne, ContinuousMap.coe_mk, dif_neg b.property]

theorem roseIntoOne_map x : roseIntoOne f r (diskRoseMap f x) =
    old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _)
      (old r (boundaryFamilyInclusion J _) x) := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective _ _ x
  cases z with
  | inl a => rfl
  | inr d =>
      change roseIntoOne f r (diskRoseMap f (cell _ _ d)) = _
      rw [diskRoseMap_cell, roseIntoOne_cell_image]
      rfl

def twoAttaching : C(BoundaryFamily (NewRelators c) (Fin 2 → ℝ),
    DiskAttachment (oneAttaching f r)) :=
  (roseIntoOne f r).comp ⟨fun z => s ⟨z.1.val, z.2⟩,
    continuous_sigma (fun k => s.continuous.comp
      (continuous_sigmaMk (σ := fun _ : K => UnitBoundary (Fin 2 → ℝ)) (i := k.val)))⟩

def oneToTarget : C(DiskAttachment (oneAttaching f r), DiskAttachment s) :=
  desc (oneAttaching f r) (boundaryFamilyInclusion _ _)
    (sourceMap f c r s h)
    ⟨fun d => old s _
      (cell _ _ ⟨d.1.val, d.2⟩),
      continuous_sigma (fun b => (old_continuous s _).comp
        ((cell_continuous _ _).comp
          (continuous_sigmaMk (σ := fun _ : B => ClosedUnitBall (Fin 1 → ℝ)) (i := b.val))))⟩
    (fun z => congrArg (old s _) (cell_boundary (roseAttaching B) _
        (boundaryFamilyInclusion_isClosedEmbedding B _).injective ⟨z.1.val, z.2⟩).symm)

@[simp] theorem oneToTarget_old x :
    oneToTarget f c r s h (old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _) x) =
      sourceMap f c r s h x := rfl

@[simp] theorem oneToTarget_cell d :
    oneToTarget f c r s h (cell (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _) d) =
      old s (boundaryFamilyInclusion K _)
        (cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨d.1.val, d.2⟩) := desc_cell ..

theorem oneToTarget_rose x :
    oneToTarget f c r s h (roseIntoOne f r x) = old s (boundaryFamilyInclusion K _) x := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective _ _ x
  cases z with
  | inl a =>
      rfl
  | inr d =>
      cases' d with b d
      by_cases hb : b ∈ Set.range f
      · obtain ⟨a, rfl⟩ := hb
        change oneToTarget f c r s h (roseIntoOne f r (cell _ _ ⟨f a, d⟩)) = _
        rw [roseIntoOne_cell_image, oneToTarget_old, sourceMap_old, diskRoseMap_cell]
        rfl
      · change oneToTarget f c r s h (roseIntoOne f r (cell _ _ ⟨b, d⟩)) = _
        rw [roseIntoOne_cell_new f r ⟨b, hb⟩ d, oneToTarget_cell]
        rfl

def extensionToTarget : C(DiskAttachment (twoAttaching f c r s), DiskAttachment s) :=
  desc (twoAttaching f c r s) (boundaryFamilyInclusion _ _)
    (oneToTarget f c r s h)
    ⟨fun d => cell s _ ⟨d.1.val, d.2⟩,
      continuous_sigma (fun k => (cell_continuous s _).comp
        (continuous_sigmaMk (σ := fun _ : K => ClosedUnitBall (Fin 2 → ℝ)) (i := k.val)))⟩
    (fun z => (oneToTarget_rose f c r s h _).trans
      (cell_boundary s _ (boundaryFamilyInclusion_isClosedEmbedding K _).injective
        _).symm)

@[simp] theorem extensionToTarget_old x :
    extensionToTarget f c r s h (old (twoAttaching f c r s)
      (boundaryFamilyInclusion (NewRelators c) _) x) = oneToTarget f c r s h x := rfl

@[simp] theorem extensionToTarget_cell d :
    extensionToTarget f c r s h (cell (twoAttaching f c r s)
      (boundaryFamilyInclusion (NewRelators c) _) d) =
      cell s (boundaryFamilyInclusion K _) ⟨d.1.val, d.2⟩ := desc_cell ..
