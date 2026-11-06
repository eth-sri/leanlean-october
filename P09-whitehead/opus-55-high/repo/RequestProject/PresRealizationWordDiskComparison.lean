import RequestProject.PresRealizationWordDisks
import RequestProject.RelatorCircleBoundaryHomeomorph


/-! Specialize the actual cone/disk comparison to the explicit relator
circle geometry. No boundary-homeomorphism input remains in this API. -/

noncomputable section
namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Topology

variable {A J : Type} (w : J → List (A × Bool)) (hw : ∀ j, w j ≠ [])

def presCircleBoundaryHomeomorph (j : J) :=
  relatorCircleBoundaryHomeomorph w j (by grind)

def actualPresWordAttaching :
    C(BoundaryFamily J (Fin 2 → ℝ), orderNerveRealization (Rose A)) :=
  presRoseDiskAttaching w (presCircleBoundaryHomeomorph w hw)

abbrev ActualPresWordDisks := DiskAttachment (actualPresWordAttaching w hw)

def actualPresWordDiskComparison :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (PresPos w)) (ActualPresWordDisks w hw) :=
  presRealizationRoseDiskHomotopyEquiv w hw _

theorem actualPresWordAttaching_apply z :
    actualPresWordAttaching w hw z =
      presCircleWordMap w z.1 ((presCircleBoundaryHomeomorph w hw z.1).symm z.2) :=
  presRoseDiskAttaching_apply w _ z

theorem actualPresWordAttaching_link j x :
    actualPresWordAttaching w hw ⟨j, presCircleBoundaryHomeomorph w hw j x⟩ =
      presCircleWordMap w j x :=
  presRoseDiskAttaching_link w _ j x

@[simp] theorem actualPresWordDiskComparison_old
    x :
    actualPresWordDiskComparison w hw (coneAdjRealizationOld (circSet w) x) =
      old (actualPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ))
        (presOldRoseHomotopyEquiv w x) :=
  presRealizationRoseDiskHomotopyEquiv_old w hw _ x
