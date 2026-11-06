import Mathlib.Tactic

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
def dummyCircleBoundaryHomeomorph  :=
  PresModel.roseFourCycle.boundaryHomeomorph.symm.trans
    (PresModel.orderRoseRealizationHomeomorph PUnit)

variable {X : Type} [TopologicalSpace X] (x : X)

def dummyOneAttaching : C(BoundaryFamily PUnit (Fin 1 → ℝ), X) :=
  ContinuousMap.const _ x

def dummyLoopMap  :=
  singletonAttachmentInto x (boundaryFamilyInclusion PUnit (Fin 1 → ℝ))
    (boundaryFamilyInclusion_isClosedEmbedding PUnit (Fin 1 → ℝ)).injective

def dummyFillingBoundary  :=
  (dummyLoopMap x).comp dummyCircleBoundaryHomeomorph.toContinuousMap

def dummyTwoAttaching  :=
  singletonDiskAttaching (dummyFillingBoundary x)



def dummyLoopPointHomeomorph  :=
  pointAttachmentBaseChangeHomeomorph x (boundaryFamilyInclusion PUnit (Fin 1 → ℝ))
    (boundaryFamilyInclusion_isClosedEmbedding PUnit (Fin 1 → ℝ)).injective



@[simp] abbrev dummyLoopPointHomeomorph_cell (y : Rose PUnit)  :=
  FiniteChains.RelativeAttachment.pointAttachmentBaseChangeHomeomorph_cell x
    (FiniteChains.RelativeAttachment.boundaryFamilyInclusion PUnit.{1} (Fin 1 → ℝ))
    FiniteChains.ClassicalGraphModel.dummyLoopMap._proof_1 y

def dummyPointFillingHomeomorph  :=
  attachmentDiagramHomeomorph
    (pointFillAttaching x (roseVertex PUnit) dummyCircleBoundaryHomeomorph)
    (unitBoundaryInclusion (Fin 2 → ℝ))
    (dummyFillingBoundary x) (unitBoundaryInclusion (Fin 2 → ℝ))
    (Equiv.refl _) (dummyLoopPointHomeomorph x) (Homeomorph.refl _)
    (fun a => dummyLoopPointHomeomorph_cell x (dummyCircleBoundaryHomeomorph a))
    (fun _ => rfl)
    (fun _ _ h => Subtype.ext (congrArg (fun z : ClosedUnitBall (Fin 2 → ℝ) => z.val) h))
    (fun _ _ h => Subtype.ext (congrArg (fun z : ClosedUnitBall (Fin 2 → ℝ) => z.val) h))

def dummyLoopFillingHomotopyEquiv  :=
  ((pointBoundaryFillingHomotopyEquiv x (roseVertex PUnit) dummyCircleBoundaryHomeomorph).trans
    (dummyPointFillingHomeomorph x).toHomotopyEquiv).trans
      (singletonDiskAttachmentHomeomorph (dummyFillingBoundary x)).symm.toHomotopyEquiv





end FiniteChains.ClassicalGraphModel
