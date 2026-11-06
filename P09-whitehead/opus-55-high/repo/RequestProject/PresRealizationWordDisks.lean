import RequestProject.ConeAdjDiskAttachment
import RequestProject.RelatorCircleFinite
import RequestProject.PresCylinderRealizationEquiv
import RequestProject.DiskFamilyHomotopyBaseChange
import RequestProject.Tac


/-! The presentation-poset realization is equivalent to actual disks
attached to its subdivided rose. The attaching map of each disk is
exactly the realized letter-reading map with the specified circle
parametrization. No presentation-to-CW comparison is assumed. -/

noncomputable section

namespace FiniteChains.PresModel
open Comb RelativeAttachment

variable {A J : Type} (w : J → List (A × Bool)) (hw : ∀ j, w j ≠ [])

local instance relatorCircleFintype j : Fintype (RelatorCircle w j) := Fintype.ofFinite _

def presOldCylinderHomeomorph :
    orderNerveRealization (ConeAdjBase (circSet w)) ≃ₜ orderNerveRealization (CylBase w) :=
  orderNerveRealizationOrderIso (coneAdjBaseOrderIso (S := circSet w))

def presOldRoseHomotopyEquiv :=
  (presOldCylinderHomeomorph w).toHomotopyEquiv.trans (presCylinderRealizationHomotopyEquiv w)

def presCircleWordMap j :
    C(orderNerveRealization (RelatorCircle w j), orderNerveRealization (Rose A)) :=
  ⟨orderNerveRealizationMap (aFun w ·.val)
      (fun _ _ h => aFun_monotone w h),
    (orderNerveRealizationMap (fun c : RelatorCircle w j => aFun w c.val)
      (fun _ _ h => aFun_monotone w h)).hom.continuous⟩

theorem presOldRoseHomotopyEquiv_link j
    x :
    presOldRoseHomotopyEquiv w
      (coneAdjRealizationAttaching (circSet w)
        ⟨j, coneAdjLinkRealizationHomeomorph (circSet w)
          (RelatorCircle w) (relatorCircleOrderIso w) j x⟩) =
      presCircleWordMap w j x := by
  have hp (c : RelatorCircle w j) :
      coneAdjBaseOrderIso (coneAdjBoundaryToBase _ j
        (coneAdjLinkOrderIso _ _ (relatorCircleOrderIso w) j c)) =
      cylOuter _ c.val := by
    apply ConeAdj.inc_injective (S := circSet w)
    exact Classical.choose_spec
      (coneAdjBoundaryToBase _ j
        (coneAdjLinkOrderIso _ _
          (relatorCircleOrderIso w) j c)).property
  rwd [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp,
    orderNerveRealizationMap_comp]
  have hf : (cylRetr _ ∘ coneAdjBaseOrderIso ∘ coneAdjBoundaryToBase _ j ∘
      coneAdjLinkOrderIso (circSet w) (RelatorCircle w) (relatorCircleOrderIso w) j) =
        (aFun w ·.val) := by
    aesop
  exact orderNerveRealizationMap_congr _ _ hf x

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  (b : ∀ j, orderNerveRealization (RelatorCircle w j) ≃ₜ UnitBoundary E)

def presCylinderDiskAttaching :=
  coneAdjDiskAttaching _ _ (relatorCircleOrderIso w) b

def presRoseDiskAttaching :=
  (presOldRoseHomotopyEquiv w).toFun.comp (presCylinderDiskAttaching w b)

omit [NormedSpace ℝ E] [ProperSpace E] in
theorem presRoseDiskAttaching_link (j : J) (x : orderNerveRealization (RelatorCircle w j)) :
    presRoseDiskAttaching w b ⟨j, b j x⟩ = presCircleWordMap w j x := by
  change presOldRoseHomotopyEquiv w
    (coneAdjDiskAttaching _ _ (relatorCircleOrderIso w) b ⟨j, b j x⟩) = _
  rwd [coneAdjDiskAttaching_link]
  exact presOldRoseHomotopyEquiv_link w j x

omit [NormedSpace ℝ E] [ProperSpace E] in
theorem presRoseDiskAttaching_apply (z : BoundaryFamily J E) :
    presRoseDiskAttaching w b z = presCircleWordMap w z.1 ((b z.1).symm z.2) := by
  cases' z with j y
  simpa [Homeomorph.apply_symm_apply] using
    presRoseDiskAttaching_link w b j ((b j).symm y)

/-- Both the cone attachment and the mapping-cylinder collapse are actual
maps; this equivalence has no unproved CW-model comparison as an input. -/
def presRealizationRoseDiskHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (PresPos w))
      (DiskAttachment (presRoseDiskAttaching w b)) := by
  letI : ∀ j, Nonempty (RelatorCircle w j) := fun j => relatorCircle_nonempty w j (hw j)
  exact (coneAdjRealizationDiskHomeomorph _ _
    _ b).toHomotopyEquiv.trans
      (diskAttachmentBaseChangeHomotopyEquiv (presCylinderDiskAttaching w b)
        (presOldRoseHomotopyEquiv w))

@[simp] theorem presRealizationRoseDiskHomotopyEquiv_old
    x :
    presRealizationRoseDiskHomotopyEquiv w hw b (coneAdjRealizationOld (circSet w) x) =
      old (presRoseDiskAttaching w b) (boundaryFamilyInclusion J E)
        (presOldRoseHomotopyEquiv w x) := by
  letI : ∀ j, Nonempty (RelatorCircle w j) := fun j => relatorCircle_nonempty w j (hw j)
  change diskAttachmentBaseChangeHomotopyEquiv _ _
    (coneAdjRealizationDiskHomeomorph _ _ _ _ (coneAdjRealizationOld _ x)) = _
  rwd [coneAdjRealizationDiskHomeomorph_old, diskAttachmentBaseChangeHomotopyEquiv_old]
  rfl
