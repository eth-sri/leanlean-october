import Mathlib.Tactic

import RequestProject.DummyLoopFilling
import RequestProject.DiskPresentationExtensionHomeomorph
import RequestProject.AttachmentLabelReindex

/-! Stabilize any literal rose-and-disks model by one fresh generator
and a disk killing exactly that generator. This gives a nonempty alphabet
even when the original graph has no non-tree edges. The homotopy
equivalence is constructed from the actual filled-loop contraction. -/

noncomputable section
namespace FiniteChains.RelativeAttachment.StabilizedDiskPresentation
open ClassicalGraphModel DiskPresentationExtension


variable {A J : Type}

def oldGenerator : A ↪ A ⊕ PUnit := ⟨Sum.inl, Sum.inl_injective⟩
def oldRelator : J ↪ J ⊕ PUnit := ⟨Sum.inl, Sum.inl_injective⟩

def freshLabelEquiv (A : Type) : {a : A ⊕ PUnit // a ∉ Set.range (Sum.inl : A → A ⊕ PUnit)} ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := ⟨Sum.inr PUnit.unit, by rintro ⟨a, ha⟩; exact Sum.inl_ne_inr ha⟩
  left_inv a := by
    rcases a with ⟨a | u, ha⟩
    · exact (ha ⟨a, rfl⟩).elim
    · cases u
      rfl
  right_inv _ := Subsingleton.elim _ _

variable (r : C(BoundaryFamily J (Fin 2 → ℝ), Rose A))

def attaching : C(BoundaryFamily (J ⊕ PUnit) (Fin 2 → ℝ), Rose (A ⊕ PUnit)) where
  toFun z := match z.1 with
    | Sum.inl j => diskRoseMap Sum.inl (r ⟨j, z.2⟩)
    | Sum.inr _ => diskRoseMap Sum.inr (dummyCircleBoundaryHomeomorph z.2)
  continuous_toFun := by
    apply continuous_sigma
    intro j
    cases j with
    | inl j => exact (diskRoseMap Sum.inl).continuous.comp (r.continuous.comp
        (continuous_sigmaMk (σ := fun _ : J => UnitBoundary (Fin 2 → ℝ)) (i := j)))
    | inr u => continuity



theorem attaching_old (z : BoundaryFamily J (Fin 2 → ℝ)) :
    diskRoseMap (oldGenerator (A := A)) (r z) = attaching r ⟨oldRelator z.1, z.2⟩ := rfl

def extension := DiskPresentationExtension.extensionModel oldGenerator oldRelator r (attaching r)
  (attaching_old r)

def basepoint  := old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) (roseVertex A)

def oneHomeomorph  :=
  diskAttachmentReindexHomeomorph
    (DiskPresentationExtension.oneAttaching oldGenerator r) (freshLabelEquiv A)



@[simp] theorem oneHomeomorph_cell (d : DiskFamily (extension r).oneCells (Fin 1 → ℝ)) :
    oneHomeomorph r
      (cell (extension r).oneAttaching (boundaryFamilyInclusion (extension r).oneCells (Fin 1 → ℝ)) d) =
        cell (dummyOneAttaching (basepoint r)) (boundaryFamilyInclusion PUnit (Fin 1 → ℝ))
          ⟨PUnit.unit, d.2⟩ := diskAttachmentReindexHomeomorph_cell ..

theorem oneHomeomorph_dummyCircle (y : Rose PUnit) :
    oneHomeomorph r
      (DiskPresentationExtension.roseIntoOne oldGenerator r (diskRoseMap Sum.inr y)) =
        dummyLoopMap (basepoint r) y := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective (roseAttaching PUnit)
    (boundaryFamilyInclusion PUnit (Fin 1 → ℝ)) y
  cases z with
  | inl u =>
      rfl
  | inr d =>
      rcases d with ⟨u, d⟩
      cases u
      change oneHomeomorph r (DiskPresentationExtension.roseIntoOne oldGenerator r
        (diskRoseMap Sum.inr (cell (roseAttaching PUnit) (boundaryFamilyInclusion PUnit _) ⟨PUnit.unit, d⟩))) = _
      rw [diskRoseMap_cell]
      let a : NewGenerators (oldGenerator (A := A)) :=
        ⟨Sum.inr PUnit.unit, by rintro ⟨a, ha⟩; exact Sum.inl_ne_inr ha⟩
      rw [DiskPresentationExtension.roseIntoOne_cell_new oldGenerator r a d]
      exact (oneHomeomorph_cell r ⟨a, d⟩).trans (singletonAttachmentInto_cell (basepoint r)
        (boundaryFamilyInclusion PUnit (Fin 1 → ℝ))
        (boundaryFamilyInclusion_isClosedEmbedding PUnit (Fin 1 → ℝ)).injective
        ⟨PUnit.unit, d⟩).symm

theorem twoAttaching_reindexed (z : BoundaryFamily (extension r).twoCells (Fin 2 → ℝ)) :
    oneHomeomorph r ((extension r).twoAttaching z) =
      dummyTwoAttaching (basepoint r) ⟨PUnit.unit, z.2⟩ := by
  rcases z with ⟨⟨j | u, hj⟩, z⟩
  · exact (hj ⟨j, rfl⟩).elim
  · cases u
    
    exact oneHomeomorph_dummyCircle r (dummyCircleBoundaryHomeomorph z)

def twoHomeomorph  :=
  attachmentDiagramHomeomorph (extension r).twoAttaching
    (boundaryFamilyInclusion (extension r).twoCells (Fin 2 → ℝ))
    (dummyTwoAttaching (basepoint r)) (boundaryFamilyInclusion PUnit (Fin 2 → ℝ))
    (sigmaLabelHomeomorph (Y := UnitBoundary (Fin 2 → ℝ)) (freshLabelEquiv J)).toEquiv
    (oneHomeomorph r)
    (sigmaLabelHomeomorph (Y := ClosedUnitBall (Fin 2 → ℝ)) (freshLabelEquiv J))
    (twoAttaching_reindexed r) (fun _ => rfl)
    (boundaryFamilyInclusion_isClosedEmbedding PUnit (Fin 2 → ℝ)).injective
    (boundaryFamilyInclusion_isClosedEmbedding (extension r).twoCells (Fin 2 → ℝ)).injective



def homotopyEquiv  :=
  ((dummyLoopFillingHomotopyEquiv (basepoint r)).trans (twoHomeomorph r).symm.toHomotopyEquiv).trans
    (DiskPresentationExtension.extensionHomeomorph oldGenerator oldRelator r (attaching r)
      (attaching_old r)).toHomotopyEquiv

theorem homotopyEquiv_toFun :
    (homotopyEquiv r).toFun =
      DiskPresentationExtension.sourceMap oldGenerator oldRelator r (attaching r) (attaching_old r) := rfl

end FiniteChains.RelativeAttachment.StabilizedDiskPresentation
