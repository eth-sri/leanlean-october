module


public import RequestProject.PointAttachmentFilling
public import RequestProject.PointAttachmentBaseChange
public import RequestProject.OrderRoseRealizationHomeomorph

@[expose] public section

/-! Adding one dummy loop and its filling disk is a genuine homotopy
equivalence on an arbitrary old space. The equivalence's forward map is
exactly the composite of the two old-space inclusions. -/

noncomputable section
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Topology

/-- An actual parametrized circle, including the direction of its
once-around traversal. It is not a chosen homotopy-type comparison. -/
def dummyCircleBoundaryHomeomorph :=
  PresModel.roseFourCycle.boundaryHomeomorph.symm.trans
    (PresModel.orderRoseRealizationHomeomorph PUnit)

variable {X : Type} [TopologicalSpace X] (x : X)

def dummyOneAttaching : C(BoundaryFamily PUnit (Fin 1 → ℝ), X) :=
  ContinuousMap.const _ x

def dummyLoopMap : C(Rose PUnit, DiskAttachment (dummyOneAttaching x)) :=
  singletonAttachmentInto x (boundaryFamilyInclusion PUnit (Fin 1 → ℝ))
    (boundaryFamilyInclusion_isClosedEmbedding PUnit (Fin 1 → ℝ)).injective

def dummyFillingBoundary :=
  (dummyLoopMap x).comp dummyCircleBoundaryHomeomorph.toContinuousMap

def dummyTwoAttaching :=
  singletonDiskAttaching (dummyFillingBoundary x)

abbrev DummyLoopFilled := DiskAttachment (dummyTwoAttaching x)

def dummyLoopPointHomeomorph :
    PointAttachment x (roseVertex PUnit) ≃ₜ DiskAttachment (dummyOneAttaching x) :=
  pointAttachmentBaseChangeHomeomorph x (boundaryFamilyInclusion PUnit (Fin 1 → ℝ))
    (boundaryFamilyInclusion_isClosedEmbedding PUnit (Fin 1 → ℝ)).injective

@[simp] theorem dummyLoopPointHomeomorph_cell (y : Rose PUnit) :
    dummyLoopPointHomeomorph x (pointCell x (roseVertex PUnit) y) = dummyLoopMap x y :=
  pointAttachmentBaseChangeHomeomorph_cell ..

def dummyPointFillingHomeomorph :=
  attachmentDiagramHomeomorph
    (pointFillAttaching x (roseVertex PUnit) dummyCircleBoundaryHomeomorph)
    (unitBoundaryInclusion (Fin 2 → ℝ))
    (dummyFillingBoundary x) (unitBoundaryInclusion (Fin 2 → ℝ))
    (Equiv.refl _) (dummyLoopPointHomeomorph x) (Homeomorph.refl _)
    (fun a => dummyLoopPointHomeomorph_cell x (dummyCircleBoundaryHomeomorph a))
    (fun _ => rfl)
    (fun _ _ h => Subtype.ext (congrArg (fun z : ClosedUnitBall (Fin 2 → ℝ) => z.val) h))
    (fun _ _ h => Subtype.ext (congrArg (fun z : ClosedUnitBall (Fin 2 → ℝ) => z.val) h))

def dummyLoopFillingHomotopyEquiv : ContinuousMap.HomotopyEquiv X (DummyLoopFilled x) :=
  ((pointBoundaryFillingHomotopyEquiv x (roseVertex PUnit) dummyCircleBoundaryHomeomorph).trans
    (dummyPointFillingHomeomorph x).toHomotopyEquiv).trans
      (singletonDiskAttachmentHomeomorph (dummyFillingBoundary x)).symm.toHomotopyEquiv

end FiniteChains.ClassicalGraphModel
