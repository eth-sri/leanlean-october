import RequestProject.HomeomorphContinuousMap
import RequestProject.PointAttachmentFilling
import RequestProject.PointAttachmentBaseChange
import RequestProject.OrderRoseRealizationHomeomorph


/-! Adding one dummy loop and its filling disk is a genuine homotopy
equivalence on an arbitrary old space. The equivalence's forward map is
exactly the composite of the two old-space inclusions. -/

noncomputable section
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment

/-- An actual parametrized circle, including the direction of its
once-around traversal. It is not a chosen homotopy-type comparison. -/
def dummyCircleBoundaryHomeomorph :=
  PresModel.roseFourCycle.boundaryHomeomorph.symm.trans
    (PresModel.orderRoseRealizationHomeomorph PUnit)

variable {X : Type} [TopologicalSpace X] (x : X)

def dummyOneAttaching : C(BoundaryFamily PUnit (Fin 1 → ℝ), X) :=
  ContinuousMap.const _ x

def dummyLoopMap : C(Rose PUnit, DiskAttachment (dummyOneAttaching x)) :=
  singletonAttachmentInto x _
    (boundaryFamilyInclusion_isClosedEmbedding PUnit _).injective

def dummyFillingBoundary :=
  (dummyLoopMap x).comp dummyCircleBoundaryHomeomorph.toContinuousMap

def dummyTwoAttaching :
    C(BoundaryFamily PUnit (Fin 2 → ℝ), DiskAttachment (dummyOneAttaching x)) :=
  singletonDiskAttaching (dummyFillingBoundary x)

abbrev DummyLoopFilled := DiskAttachment (dummyTwoAttaching x)

def dummyLoopPointHomeomorph :
    PointAttachment x (roseVertex PUnit) ≃ₜ DiskAttachment (dummyOneAttaching x) :=
  pointAttachmentBaseChangeHomeomorph x _
    (boundaryFamilyInclusion_isClosedEmbedding PUnit _).injective


@[simp] theorem dummyLoopPointHomeomorph_cell y :
    dummyLoopPointHomeomorph x (pointCell x (roseVertex PUnit) y) = dummyLoopMap x y :=
  pointAttachmentBaseChangeHomeomorph_cell ..

def dummyPointFillingHomeomorph :
    FilledPointAttachment x (roseVertex PUnit) dummyCircleBoundaryHomeomorph
        (unitBoundaryInclusion (Fin 2 → ℝ)) ≃ₜ
      Space (dummyFillingBoundary x) (unitBoundaryInclusion (Fin 2 → ℝ)) :=
  attachmentDiagramHomeomorph
    (pointFillAttaching x (roseVertex PUnit) dummyCircleBoundaryHomeomorph)
    (unitBoundaryInclusion (Fin 2 → ℝ))
    (dummyFillingBoundary x) (unitBoundaryInclusion (Fin 2 → ℝ))
    (Equiv.refl _) (dummyLoopPointHomeomorph x) (Homeomorph.refl _)
    (fun a => dummyLoopPointHomeomorph_cell x (dummyCircleBoundaryHomeomorph a))
    (by simp)
    (fun _ _ h => Subtype.ext (congrArg (·.val) h))
    (fun _ _ h => Subtype.ext (congrArg (·.val) h))

def dummyLoopFillingHomotopyEquiv : ContinuousMap.HomotopyEquiv X (DummyLoopFilled x) :=
  ((pointBoundaryFillingHomotopyEquiv x _ dummyCircleBoundaryHomeomorph).trans
    (dummyPointFillingHomeomorph x).toHomotopyEquiv).trans
      (singletonDiskAttachmentHomeomorph _).symm.toHomotopyEquiv

def dummyLoopFillingOld : C(X, DummyLoopFilled x) :=
  (⟨old _ _,
    old_continuous _ _⟩ : C(DiskAttachment (dummyOneAttaching x), _)).comp
      ⟨old _ _, old_continuous _ _⟩

