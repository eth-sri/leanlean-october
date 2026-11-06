import Mathlib.Tactic

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

abbrev SingletonAttachment (i : A → D) := Space (fun _ : A => (PUnit.unit : PUnit)) i

def singletonAttachmentPoint (i : A → D)  :=
  old (fun _ : A => (PUnit.unit : PUnit)) i PUnit.unit

variable (x : X)
def singletonAttachmentInto  (i : A → D) (hi : Function.Injective i) :
    C(SingletonAttachment i, Space (fun _ : A => x) i) :=
  attachmentBaseMap (fun _ : A => (PUnit.unit : PUnit)) i hi (ContinuousMap.const PUnit x)

theorem singletonAttachmentInto_injective  (i : A → D) (hi : Function.Injective i) :
    Function.Injective (singletonAttachmentInto x i hi) :=
  attachmentBaseMap_injective _ _ hi _ (fun _ _ _ => Subsingleton.elim _ _)



@[simp] theorem singletonAttachmentInto_cell  (i : A → D) (hi : Function.Injective i) (d : D) :
    singletonAttachmentInto x i hi (cell (fun _ : A => (PUnit.unit : PUnit)) i d) =
      cell (fun _ : A => x) i d := attachmentBaseMap_cell ..

theorem singletonAttachmentInto_mem_old_iff  (i : A → D) (hi : Function.Injective i)
    (z : SingletonAttachment i) :
    singletonAttachmentInto x i hi z ∈ Set.range (old (fun _ : A => x) i) ↔
      z = singletonAttachmentPoint i := by
  rcases z with p | d
  · aesop
  · constructor
    · rintro ⟨y, hy⟩
      change Sum.inl y = cell (fun _ : A => x) i d.val at hy
      rw [cell_of_not_mem _ _ _ d.property] at hy
      exact (Sum.inl_ne_inr hy).elim
    · intro hz
      exact (Sum.inr_ne_inl hz).elim

theorem singletonAttachment_piece_isQuotientMap  (i : A → D) (hi : Function.Injective i) :
    IsQuotientMap (Sum.elim (old (fun _ : A => x) i) (singletonAttachmentInto x i hi)) := by
  let F : C(X ⊕ D, X ⊕ SingletonAttachment i) :=
    ⟨Sum.elim Sum.inl (fun d => Sum.inr (cell (fun _ : A => (PUnit.unit : PUnit)) i d)),
      continuous_inl.sumElim (continuous_inr.comp (cell_continuous _ _))⟩
  let Q : C(X ⊕ SingletonAttachment i, Space (fun _ : A => x) i) :=
    ⟨Sum.elim (old (fun _ : A => x) i) (singletonAttachmentInto x i hi),
      (old_continuous _ _).sumElim (singletonAttachmentInto x i hi).continuous⟩
  have hf : Q ∘ F = quotientMap (fun _ : A => x) i := by
    aesop
  apply IsQuotientMap.of_comp F.continuous Q.continuous
  rw [hf]
  exact attachmentQuotientMap_isQuotientMap _ _

def pointAttachmentBaseChangeHomeomorph  (i : A → D) (hi : Function.Injective i)  :=
  attachmentQuotientHomeomorph (fun _ : PUnit => x) (fun _ : PUnit => singletonAttachmentPoint i)
    ⟨old (fun _ : A => x) i, old_continuous _ _⟩ (singletonAttachmentInto x i hi)
    (fun _ => rfl) (old_injective _ _)
    (fun z => by
      dsimp
      rw [singletonAttachmentInto_mem_old_iff x i hi]
      constructor
      · exact fun hz => ⟨PUnit.unit, hz.symm⟩
      · rintro ⟨a, ha⟩
        exact ha.symm)
    (fun _ _ _ _ h => singletonAttachmentInto_injective x i hi h)
    (singletonAttachment_piece_isQuotientMap x i hi)



@[simp] theorem pointAttachmentBaseChangeHomeomorph_cell
     (i : A → D) (hi : Function.Injective i) (y : SingletonAttachment i) :
    pointAttachmentBaseChangeHomeomorph x i hi (pointCell x (singletonAttachmentPoint i) y) =
      singletonAttachmentInto x i hi y := attachmentQuotientHomeomorph_cell ..

def sigmaSingletonHomeomorph (Y : Type u) [TopologicalSpace Y] :
    (Σ _ : PUnit.{u + 1}, Y) ≃ₜ Y where
  toFun z := z.2
  invFun y := ⟨PUnit.unit, y⟩
  left_inv := by rintro ⟨u, y⟩; cases u; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_sigma (fun _ => continuous_id)
  continuous_invFun := continuous_sigmaMk (σ := fun _ : PUnit.{u + 1} => Y) (i := PUnit.unit)

variable {E : Type u} [NormedAddCommGroup E]

  (r : C(UnitBoundary E, X))
def singletonDiskAttaching   :=
  r.comp (sigmaSingletonHomeomorph (UnitBoundary E)).toContinuousMap

def singletonDiskAttachmentHomeomorph   :=
  attachmentDiagramHomeomorph (singletonDiskAttaching r) (boundaryFamilyInclusion PUnit E)
    r (unitBoundaryInclusion E) (sigmaSingletonHomeomorph (UnitBoundary E)).toEquiv
    (Homeomorph.refl X) (sigmaSingletonHomeomorph (ClosedUnitBall E))
    (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h => Subtype.ext (congrArg (fun z : ClosedUnitBall E => z.val) h))
    (boundaryFamilyInclusion_isClosedEmbedding PUnit E).injective





end FiniteChains.RelativeAttachment
