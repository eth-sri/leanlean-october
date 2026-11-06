module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.PresRealizationWordDiskComparison
public import RequestProject.OrderRoseRealizationHomeomorph

@[expose] public section

/-! A presentation realization and a literal bouquet of interval circles
with genuine two-disks have a constructed homotopy equivalence. All cone,
circle and bouquet identifications are instantiated by explicit maps. -/

noncomputable section
namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Topology

variable {A J : Type} (w : J → List (A × Bool)) (hw : ∀ j, w j ≠ [])

def classicalPresWordAttaching :
    C(BoundaryFamily J (Fin 2 → ℝ), ClassicalGraphModel.Rose A) :=
  (orderRoseRealizationHomeomorph A).toContinuousMap.comp (actualPresWordAttaching w hw)

abbrev ClassicalPresWordDisks := DiskAttachment (classicalPresWordAttaching w hw)

def presClassicalDiskComparison :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (PresPos w)) (ClassicalPresWordDisks w hw) :=
  (actualPresWordDiskComparison w hw).trans
    (diskAttachmentBaseChangeHomotopyEquiv (actualPresWordAttaching w hw)
      (orderRoseRealizationHomeomorph A).toHomotopyEquiv)

theorem classicalPresWordAttaching_link (j : J) (x : orderNerveRealization (RelatorCircle w j)) :
    classicalPresWordAttaching w hw ⟨j, presCircleBoundaryHomeomorph w hw j x⟩ =
      orderRoseRealizationHomeomorph A (presCircleWordMap w j x) := by
  change orderRoseRealizationHomeomorph A
    (actualPresWordAttaching w hw ⟨j, presCircleBoundaryHomeomorph w hw j x⟩) = _
  rw [actualPresWordAttaching_link]
