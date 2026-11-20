module


public import RequestProject.PointAttachmentHomotopyEquiv
public import RequestProject.AttachmentQuotientHomeomorph
public import RequestProject.AttachmentDiagramHomeomorph
public import RequestProject.ClassicalCellAttachmentMaps

@[expose] public section

/-! Changing the single old point of a pointed attachment to an
arbitrary space is the actual pushout at that point. This identifies a
literal one-cell loop with its pointed circle, without a classification
or homotopy-type premise. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open Topology
open scoped Topology

universe u
variable {A D P K X : Type u}
  [TopologicalSpace D] [TopologicalSpace P] [TopologicalSpace K] [TopologicalSpace X]

theorem attachmentBaseMap_injective (r : A → P) (i : A → D) (hi : Function.Injective i)
    (e : C(P, K)) (he : Function.Injective e) :
    Function.Injective (attachmentBaseMap r i hi e) := by
  rintro (p | d) (q | u) h
  · exact congrArg Sum.inl (he (Sum.inl.inj h))
  · change Sum.inl _ = cell _ i u.val at h
    aesop
  · change cell _ i d.val = Sum.inl _ at h
    aesop
  · change cell _ i d.val = cell _ i u.val at h
    grind [cell_of_not_mem]

variable (i : A → D)

abbrev SingletonAttachment := Space (fun _ : A => PUnit.unit) i

def singletonAttachmentPoint :=
  old (fun _ : A => PUnit.unit) i PUnit.unit

variable (x : X) (i : A → D) (hi : Function.Injective i)

def singletonAttachmentInto :
    C(SingletonAttachment i, Space (fun _ : A => x) i) :=
  attachmentBaseMap _ i hi (ContinuousMap.const PUnit x)

theorem singletonAttachmentInto_injective :
    Function.Injective (singletonAttachmentInto x i hi) :=
  by solve_by_elim [attachmentBaseMap_injective]

@[simp] theorem singletonAttachmentInto_point :
    singletonAttachmentInto x i hi (singletonAttachmentPoint i) = old _ i x := rfl

@[simp] theorem singletonAttachmentInto_cell (d : D) :
    singletonAttachmentInto x i hi (cell (fun _ : A => PUnit.unit) i d) =
      cell _ i d := attachmentBaseMap_cell ..

theorem singletonAttachmentInto_mem_old_iff
    (z : SingletonAttachment i) :
    singletonAttachmentInto x i hi z ∈ Set.range (old (fun _ : A => x) i) ↔
      z = singletonAttachmentPoint i := by
  rcases z with p | d
  · aesop
  · constructor
    · rintro ⟨y, hy⟩
      change Sum.inl y = cell _ i d.val at hy
      aesop
    · simp_all

theorem singletonAttachment_piece_isQuotientMap :
    IsQuotientMap (Sum.elim (old (fun _ : A => x) i) (singletonAttachmentInto x i hi)) := by
  let F : C(X ⊕ D, X ⊕ SingletonAttachment i) :=
    ⟨Sum.elim Sum.inl _,
      continuous_inl.sumElim (continuous_inr.comp (cell_continuous _ _))⟩
  let Q : C(X ⊕ SingletonAttachment i, Space _ i) :=
    ⟨Sum.elim _ _,
      (old_continuous _ _).sumElim (singletonAttachmentInto x i hi).continuous⟩
  have hf : Q ∘ F = quotientMap _ i := by
    aesop
  apply IsQuotientMap.of_comp F.continuous Q.continuous
  rw [hf]
  exact attachmentQuotientMap_isQuotientMap _ _

def pointAttachmentBaseChangeHomeomorph :=
  attachmentQuotientHomeomorph (fun _ : PUnit => x) (fun _ : PUnit => singletonAttachmentPoint i)
    ⟨old (fun _ : A => x) i, old_continuous _ _⟩ _
    (fun _ => rfl) (old_injective _ _)
    (fun z => by
      change singletonAttachmentInto x i hi z ∈ Set.range (old (fun _ : A => x) i) ↔
        z ∈ Set.range (fun _ : PUnit.{u + 1} => singletonAttachmentPoint i)
      grind [singletonAttachmentInto_mem_old_iff])
    (fun _ _ _ _ h => singletonAttachmentInto_injective x i hi h)
    (singletonAttachment_piece_isQuotientMap x i hi)

@[simp] theorem pointAttachmentBaseChangeHomeomorph_old (y : X) :
    pointAttachmentBaseChangeHomeomorph x i hi (pointOld x (singletonAttachmentPoint i) y) =
      old _ i y := rfl

@[simp] theorem pointAttachmentBaseChangeHomeomorph_cell (y : SingletonAttachment i) :
    pointAttachmentBaseChangeHomeomorph x i hi (pointCell x (singletonAttachmentPoint i) y) =
      singletonAttachmentInto x i hi y := attachmentQuotientHomeomorph_cell ..

def sigmaSingletonHomeomorph (Y : Type u) [TopologicalSpace Y] :
    (Σ _ : PUnit.{u + 1}, Y) ≃ₜ Y where
  toFun z := z.2
  invFun y := ⟨PUnit.unit, y⟩
  left_inv := by solve_by_elim
  right_inv _ := rfl
  continuous_toFun := continuous_sigma (fun _ => continuous_id)
  continuous_invFun := continuous_sigmaMk (σ := fun _ : PUnit.{u + 1} => Y) (i := PUnit.unit)

variable {E : Type u} [NormedAddCommGroup E]

variable (r : C(UnitBoundary E, X))

def singletonDiskAttaching :=
  r.comp (sigmaSingletonHomeomorph (UnitBoundary E)).toContinuousMap

def singletonDiskAttachmentHomeomorph :=
  attachmentDiagramHomeomorph (singletonDiskAttaching r) _
    r (unitBoundaryInclusion E) _
    (Homeomorph.refl X) (sigmaSingletonHomeomorph (ClosedUnitBall E))
    (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h => Subtype.ext (congrArg (fun z : ClosedUnitBall E => z.val) h))
    (boundaryFamilyInclusion_isClosedEmbedding PUnit E).injective

@[simp] theorem singletonDiskAttachmentHomeomorph_old (x : X) :
    singletonDiskAttachmentHomeomorph r (old (singletonDiskAttaching r) (boundaryFamilyInclusion PUnit E) x) =
      old r _ x := rfl

@[simp] theorem singletonDiskAttachmentHomeomorph_cell (d : DiskFamily PUnit E) :
    singletonDiskAttachmentHomeomorph r
      (cell (singletonDiskAttaching r) (boundaryFamilyInclusion PUnit E) d) =
      cell r _ d.2 := attachmentDiagramHomeomorph_cell ..

end FiniteChains.RelativeAttachment
