module

public import RequestProject.HomeomorphContinuousMap
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
  · change Sum.inl (e p) = cell (e ∘ r) i u.val at h
    rw [cell_of_not_mem _ _ _ u.property] at h
    exact (Sum.inl_ne_inr h).elim
  · change cell (e ∘ r) i d.val = Sum.inl (e q) at h
    rw [cell_of_not_mem _ _ _ d.property] at h
    exact (Sum.inr_ne_inl h).elim
  · change cell (e ∘ r) i d.val = cell (e ∘ r) i u.val at h
    rw [cell_of_not_mem _ _ _ d.property, cell_of_not_mem _ _ _ u.property] at h
    exact congrArg Sum.inr (Sum.inr.inj h)

abbrev SingletonAttachment (i : A → D) := Space (fun _  => PUnit.unit) i

def singletonAttachmentPoint (i : A → D) : SingletonAttachment i :=
  old (fun _  => PUnit.unit) i PUnit.unit

def singletonAttachmentInto (x : X) (i : A → D) (hi : Function.Injective i) :
    C(SingletonAttachment i, Space (fun _ : A => x) i) :=
  attachmentBaseMap (fun _  => PUnit.unit) i hi (ContinuousMap.const PUnit x)

theorem singletonAttachmentInto_injective (x : X) (i : A → D) (hi : Function.Injective i) :
    Function.Injective (singletonAttachmentInto x i hi) :=
  attachmentBaseMap_injective _ _ hi _ (fun _ _ _ => Subsingleton.elim _ _)


@[simp] theorem singletonAttachmentInto_cell (x : X) (i : A → D) (hi : Function.Injective i) (d : D) :
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
      change Sum.inl y = cell (fun _  => x) i d.val at hy
      aesop
    · tauto

theorem singletonAttachment_piece_isQuotientMap (x : X) (i : A → D) (hi : Function.Injective i) :
    IsQuotientMap (Sum.elim (old (fun _ : A => x) i) (singletonAttachmentInto x i hi)) := by
  let F : C(X ⊕ D, X ⊕ SingletonAttachment i) :=
    ⟨Sum.elim Sum.inl (fun d => Sum.inr (cell (fun _  => PUnit.unit) i d)),
      continuous_inl.sumElim (continuous_inr.comp (cell_continuous _ _))⟩
  let Q : C(X ⊕ SingletonAttachment i, Space (fun _  => x) i) :=
    ⟨Sum.elim (old (fun _  => x) i) (singletonAttachmentInto x i hi),
      (old_continuous _ _).sumElim (singletonAttachmentInto x i hi).continuous⟩
  have hf : Q ∘ F = quotientMap (fun _  => x) i := by
    funext z
    cases z with
    | inl y => rfl
    | inr d => exact singletonAttachmentInto_cell x i hi d
  apply IsQuotientMap.of_comp F.continuous Q.continuous
  rw [hf]
  exact attachmentQuotientMap_isQuotientMap _ _

def pointAttachmentBaseChangeHomeomorph (x : X) (i : A → D) (hi : Function.Injective i) :
    PointAttachment x (singletonAttachmentPoint i) ≃ₜ Space (fun _ : A => x) i :=
  attachmentQuotientHomeomorph (fun _  => x) (fun _  => singletonAttachmentPoint i)
    (Space.oldMap (fun _  => x) i) (singletonAttachmentInto x i hi)
    (fun _ => rfl) (old_injective _ _)
    (fun z => by
      simp_all [singletonAttachmentInto_mem_old_iff x i hi])
    (fun _ _ _ _ h => singletonAttachmentInto_injective x i hi h)
    (singletonAttachment_piece_isQuotientMap x i hi)



@[simp] theorem pointAttachmentBaseChangeHomeomorph_cell
    (x : X) (i : A → D) (hi : Function.Injective i) (y : SingletonAttachment i) :
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
  r.comp (sigmaSingletonHomeomorph (UnitBoundary E)).toContinuousMap

def singletonDiskAttachmentHomeomorph (r : C(UnitBoundary E, X)) :
    DiskAttachment (singletonDiskAttaching r) ≃ₜ Space r (unitBoundaryInclusion E) :=
  attachmentDiagramHomeomorph (singletonDiskAttaching r) (boundaryFamilyInclusion PUnit E)
    r (unitBoundaryInclusion E) (sigmaSingletonHomeomorph (UnitBoundary E)).toEquiv
    (Homeomorph.refl X) (sigmaSingletonHomeomorph (ClosedUnitBall E))
    (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h => Subtype.ext (congrArg (·.val) h))
    (boundaryFamilyInclusion_isClosedEmbedding PUnit E).injective




end FiniteChains.RelativeAttachment
