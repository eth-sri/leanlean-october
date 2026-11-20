module

public import RequestProject.PresRealizationWordDisks
public import RequestProject.RelatorCircleBoundaryHomeomorph

@[expose] public section

/-! Specialize the actual cone/disk comparison to the explicit relator
circle geometry. No boundary-homeomorphism input remains in this API. -/

noncomputable section
namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Topology

variable {A J : Type} (w : J → List (A × Bool)) (hw : ∀ j, w j ≠ [])

def presCircleBoundaryHomeomorph (j : J) :=
  relatorCircleBoundaryHomeomorph w j (List.length_pos_of_ne_nil (hw j))

def actualPresWordAttaching :=
  presRoseDiskAttaching w (presCircleBoundaryHomeomorph w hw)

abbrev ActualPresWordDisks := DiskAttachment (actualPresWordAttaching w hw)

def actualPresWordDiskComparison :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (PresPos w)) (ActualPresWordDisks w hw) :=
  presRealizationRoseDiskHomotopyEquiv w hw _

theorem actualPresWordAttaching_apply (z : BoundaryFamily J (Fin 2 → ℝ)) :
    actualPresWordAttaching w hw z =
      presCircleWordMap w z.1 ((presCircleBoundaryHomeomorph w hw z.1).symm z.2) :=
  by apply presRoseDiskAttaching_apply

theorem actualPresWordAttaching_link (j : J) (x : orderNerveRealization (RelatorCircle w j)) :
    actualPresWordAttaching w hw ⟨j, presCircleBoundaryHomeomorph w hw j x⟩ =
      presCircleWordMap w j x :=
  by apply presRoseDiskAttaching_link

@[simp] theorem actualPresWordDiskComparison_old
    (x : orderNerveRealization (ConeAdjBase _)) :
    actualPresWordDiskComparison w hw (coneAdjRealizationOld (circSet w) x) =
      old _ _
        (presOldRoseHomotopyEquiv w x) :=
  presRealizationRoseDiskHomotopyEquiv_old w hw _ x

end FiniteChains.PresModel
