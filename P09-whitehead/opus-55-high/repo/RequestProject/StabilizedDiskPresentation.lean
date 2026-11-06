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
open scoped Classical Topology

variable {A J : Type}

def oldGenerator : A ↪ A ⊕ PUnit := ⟨Sum.inl, Sum.inl_injective⟩
def oldRelator : J ↪ J ⊕ PUnit := ⟨Sum.inl, Sum.inl_injective⟩

def freshLabelEquiv (A : Type) : {a : A ⊕ PUnit // a ∉ Set.range (Sum.inl : A → A ⊕ PUnit)} ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := ⟨Sum.inr PUnit.unit, by simp⟩
  left_inv a := by
    grind
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
    | inr u => exact (diskRoseMap Sum.inr).continuous.comp dummyCircleBoundaryHomeomorph.continuous

abbrev Model := DiskAttachment (attaching r)

theorem attaching_old z :
    diskRoseMap (oldGenerator (A := A)) (r z) = attaching r ⟨oldRelator z.1, z.2⟩ := rfl

def extension := DiskPresentationExtension.extensionModel oldGenerator oldRelator r _
  (attaching_old r)

def basepoint : DiskAttachment r := old r _ (roseVertex A)

def oneHomeomorph :
    DiskAttachment (extension r).oneAttaching ≃ₜ DiskAttachment (dummyOneAttaching (basepoint r)) :=
  diskAttachmentReindexHomeomorph
    (DiskPresentationExtension.oneAttaching oldGenerator r) (freshLabelEquiv A)


@[simp] theorem oneHomeomorph_cell d :
    oneHomeomorph r
      (cell (extension r).oneAttaching (boundaryFamilyInclusion (extension r).oneCells (Fin 1 → ℝ)) d) =
        cell (dummyOneAttaching (basepoint r)) (boundaryFamilyInclusion PUnit (Fin 1 → ℝ))
          ⟨PUnit.unit, d.2⟩ := diskAttachmentReindexHomeomorph_cell ..

theorem oneHomeomorph_dummyCircle y :
    oneHomeomorph r
      (DiskPresentationExtension.roseIntoOne oldGenerator r (diskRoseMap Sum.inr y)) =
        dummyLoopMap (basepoint r) y := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective _
    _ y
  cases z with
  | inl u =>
      rfl
  | inr d =>
      cases' d with u d
      cases u
      change oneHomeomorph r (DiskPresentationExtension.roseIntoOne oldGenerator r
        (diskRoseMap Sum.inr (cell _ _ ⟨PUnit.unit, d⟩))) = _
      rw [diskRoseMap_cell]
      let a : NewGenerators (oldGenerator (A := A)) :=
        ⟨Sum.inr PUnit.unit, by rintro ⟨a, ha⟩; exact Sum.inl_ne_inr ha⟩
      rw [DiskPresentationExtension.roseIntoOne_cell_new oldGenerator r a d]
      exact (oneHomeomorph_cell r _).trans (singletonAttachmentInto_cell _
        _
        _
        _).symm

theorem twoAttaching_reindexed z :
    oneHomeomorph r ((extension r).twoAttaching z) =
      dummyTwoAttaching (basepoint r) ⟨PUnit.unit, z.2⟩ := by
  rcases z with ⟨⟨j | u, hj⟩, z⟩
  · tauto
  · cases u
    exact oneHomeomorph_dummyCircle r _

def twoHomeomorph : DiskAttachment (extension r).twoAttaching ≃ₜ DummyLoopFilled (basepoint r) :=
  attachmentDiagramHomeomorph _
    _
    _ _
    (sigmaLabelHomeomorph (Y := UnitBoundary (Fin 2 → ℝ)) (freshLabelEquiv J)).toEquiv
    _
    (sigmaLabelHomeomorph (Y := ClosedUnitBall (Fin 2 → ℝ)) (freshLabelEquiv J))
    (twoAttaching_reindexed r) (by aesop)
    (boundaryFamilyInclusion_isClosedEmbedding PUnit _).injective
    (boundaryFamilyInclusion_isClosedEmbedding _ _).injective


def homotopyEquiv : ContinuousMap.HomotopyEquiv (DiskAttachment r) (Model r) :=
  ((dummyLoopFillingHomotopyEquiv _).trans (twoHomeomorph r).symm.toHomotopyEquiv).trans
    (DiskPresentationExtension.extensionHomeomorph oldGenerator oldRelator r _
      (attaching_old r)).toHomotopyEquiv

