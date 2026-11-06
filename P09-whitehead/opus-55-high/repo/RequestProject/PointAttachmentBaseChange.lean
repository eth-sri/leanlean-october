import RequestProject.HomeomorphContinuousMap
import RequestProject.PointAttachmentHomotopyEquiv
import RequestProject.AttachmentQuotientHomeomorph
import RequestProject.AttachmentDiagramHomeomorph
import RequestProject.ClassicalCellAttachmentMaps


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

theorem attachmentBaseMap_injective r (i : A → D) hi
    (e : C(P, K)) (he : Function.Injective e) :
    Function.Injective (attachmentBaseMap r i hi e) := by
  rintro (p | d) (q | u) h
  · exact congrArg Sum.inl (he (Sum.inl.inj h))
  · change Sum.inl (e p) = cell _ i u.val at h
    aesop
  · change cell _ i d.val = Sum.inl (e q) at h
    aesop
  · change cell _ i d.val = cell _ i u.val at h
    grind [cell_of_not_mem _ _ _ d.property, cell_of_not_mem _ _ _ u.property]

abbrev SingletonAttachment (i : A → D) := Space (fun _ : A => (PUnit.unit : PUnit)) i

def singletonAttachmentPoint (i : A → D) : SingletonAttachment i :=
  old (fun _ : A => (PUnit.unit : PUnit)) i PUnit.unit

def singletonAttachmentInto (x : X) (i : A → D) (hi : Function.Injective i) :
    C(SingletonAttachment i, Space (fun _ : A => x) i) :=
  attachmentBaseMap (fun _ : A => (PUnit.unit : PUnit)) i hi (ContinuousMap.const PUnit x)

theorem singletonAttachmentInto_injective (x : X) (i : A → D) hi :
    Function.Injective (singletonAttachmentInto x i hi) :=
  attachmentBaseMap_injective _ _ hi _ (by tauto)


@[simp] theorem singletonAttachmentInto_cell (x : X) (i : A → D) (hi : Function.Injective i) d :
    singletonAttachmentInto x i hi (cell (fun _ : A => (PUnit.unit : PUnit)) i d) =
      cell (fun _ : A => x) i d := attachmentBaseMap_cell ..

theorem singletonAttachmentInto_mem_old_iff (x : X) (i : A → D) (hi : Function.Injective i)
    (z : SingletonAttachment i) :
    singletonAttachmentInto x i hi z ∈ Set.range (old (fun _ : A => x) i) ↔
      z = singletonAttachmentPoint i := by
  rcases z with p | d
  · tauto
  · constructor
    · rintro ⟨y, hy⟩
      change Sum.inl y = cell _ i d.val at hy
      aesop
    tauto

theorem singletonAttachment_piece_isQuotientMap (x : X) (i : A → D) (hi : Function.Injective i) :
    IsQuotientMap (Sum.elim (old (fun _ : A => x) i) (singletonAttachmentInto x i hi)) := by
  let F : C(X ⊕ D, X ⊕ SingletonAttachment i) :=
    ⟨Sum.elim Sum.inl (fun d => Sum.inr (cell _ i d)),
      continuous_inl.sumElim (continuous_inr.comp (cell_continuous _ _))⟩
  let Q : C(X ⊕ SingletonAttachment i, Space (fun _ => x) i) :=
    ⟨Sum.elim (old _ i) (singletonAttachmentInto x i hi),
      (old_continuous _ _).sumElim (singletonAttachmentInto x i hi).continuous⟩
  have hf : Q ∘ F = quotientMap _ i := by
    aesop
  apply IsQuotientMap.of_comp F.continuous Q.continuous
  rw [hf]
  exact attachmentQuotientMap_isQuotientMap _ _

def pointAttachmentBaseChangeHomeomorph (x : X) (i : A → D) (hi : Function.Injective i) :
    PointAttachment x (singletonAttachmentPoint i) ≃ₜ Space (fun _ : A => x) i :=
  attachmentQuotientHomeomorph (fun _ : PUnit => x) (fun _ : PUnit => singletonAttachmentPoint i)
    ⟨old (fun _ : A => x) i, old_continuous _ _⟩ (singletonAttachmentInto x i hi)
    (by tauto) (old_injective _ _)
    (fun z => by
      simp [singletonAttachmentInto_mem_old_iff x i hi])
    (fun _ _ _ _ h => singletonAttachmentInto_injective x i hi h)
    (singletonAttachment_piece_isQuotientMap x i hi)

@[simp] theorem pointAttachmentBaseChangeHomeomorph_old
    x (i : A → D) (hi : Function.Injective i) (y : X) :
    pointAttachmentBaseChangeHomeomorph x i hi (pointOld x (singletonAttachmentPoint i) y) =
      old (fun _ : A => x) i y := attachmentQuotientHomeomorph_old ..

@[simp] theorem pointAttachmentBaseChangeHomeomorph_cell
    (x : X) (i : A → D) hi y :
    pointAttachmentBaseChangeHomeomorph x i hi (pointCell x (singletonAttachmentPoint i) y) =
      singletonAttachmentInto x i hi y := attachmentQuotientHomeomorph_cell ..

def sigmaSingletonHomeomorph (Y : Type u) [TopologicalSpace Y] :
    (Σ _ : PUnit.{u + 1}, Y) ≃ₜ Y where
  toFun z := z.2
  invFun y := ⟨PUnit.unit, y⟩
  left_inv := by tauto
  right_inv _ := rfl
  continuous_toFun := continuous_sigma (fun _ => continuous_id)
  continuous_invFun := continuous_sigmaMk (σ := fun _ : PUnit.{u + 1} => Y) (i := PUnit.unit)

variable {E : Type u} [NormedAddCommGroup E]

def singletonDiskAttaching (r : C(UnitBoundary E, X)) : C(BoundaryFamily PUnit E, X) :=
  r.comp (sigmaSingletonHomeomorph _).toContinuousMap

def singletonDiskAttachmentHomeomorph (r : C(UnitBoundary E, X)) :
    DiskAttachment (singletonDiskAttaching r) ≃ₜ Space r (unitBoundaryInclusion E) :=
  attachmentDiagramHomeomorph (singletonDiskAttaching r) (boundaryFamilyInclusion PUnit E)
    r (unitBoundaryInclusion E) (sigmaSingletonHomeomorph _).toEquiv
    (Homeomorph.refl X) (sigmaSingletonHomeomorph _)
    (by tauto) (by tauto)
    (fun _ _ h => Subtype.ext (congrArg (·.val) h))
    (boundaryFamilyInclusion_isClosedEmbedding PUnit E).injective

