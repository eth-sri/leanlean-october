module

public import RequestProject.ConeAdjDiskAttachment
public import RequestProject.RelatorCircleFinite
public import RequestProject.PresCylinderRealizationEquiv
public import RequestProject.DiskFamilyHomotopyBaseChange

@[expose] public section

/-! The presentation-poset realization is equivalent to actual disks
attached to its subdivided rose. The attaching map of each disk is
exactly the realized letter-reading map with the specified circle
parametrization. No presentation-to-CW comparison is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Topology

variable {A J : Type} (w : J → List (A × Bool)) (hw : ∀ j, w j ≠ [])

local instance relatorCircleFintype (j : J) : Fintype (RelatorCircle w j) := Fintype.ofFinite _

def presOldCylinderHomeomorph :=
  orderNerveRealizationOrderIso (coneAdjBaseOrderIso (S := circSet w))

def presOldRoseHomotopyEquiv :=
  (presOldCylinderHomeomorph w).toHomotopyEquiv.trans (presCylinderRealizationHomotopyEquiv w)

variable (j : J)

def presCircleWordMap :
    C(orderNerveRealization (RelatorCircle w j), orderNerveRealization (Rose A)) :=
  ⟨orderNerveRealizationMap (fun c : RelatorCircle w j => aFun w c.val)
      _,
    (orderNerveRealizationMap (fun c : RelatorCircle w j => aFun w c.val)
      (fun _ _ h => aFun_monotone w h)).hom.continuous⟩

theorem presOldRoseHomotopyEquiv_link
    (x : orderNerveRealization (RelatorCircle w j)) :
    presOldRoseHomotopyEquiv w
      (coneAdjRealizationAttaching (circSet w)
        ⟨j, coneAdjLinkRealizationHomeomorph (circSet w)
          (RelatorCircle w) (relatorCircleOrderIso w) j x⟩) =
      presCircleWordMap w j x := by
  have hp (c : RelatorCircle w j) :
      coneAdjBaseOrderIso (coneAdjBoundaryToBase _ j
        (coneAdjLinkOrderIso (circSet w) (RelatorCircle w) (relatorCircleOrderIso w) j c)) =
      cylOuter (aHom w) c.val := by
    apply ConeAdj.inc_injective
    exact Classical.choose_spec
      (coneAdjBoundaryToBase _ j
        (coneAdjLinkOrderIso _ _
          _ j c)).property
  erw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp,
    orderNerveRealizationMap_comp]
  have hf : (cylRetr _ ∘ coneAdjBaseOrderIso ∘ coneAdjBoundaryToBase _ j ∘
      coneAdjLinkOrderIso _ _ (relatorCircleOrderIso w) j) =
        (fun c : RelatorCircle w j => aFun w c.val) := by
    funext c
    aesop
  apply orderNerveRealizationMap_congr <;> assumption

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
    (coneAdjDiskAttaching (circSet w) (RelatorCircle w) (relatorCircleOrderIso w) b ⟨j, b j x⟩) = _
  simp_all [coneAdjDiskAttaching_link, presOldRoseHomotopyEquiv_link]

omit [NormedSpace ℝ E] [ProperSpace E] in
theorem presRoseDiskAttaching_apply (z : BoundaryFamily J E) :
    presRoseDiskAttaching w b z = presCircleWordMap w z.1 ((b z.1).symm z.2) := by
  rcases z with ⟨j, y⟩
  simpa only [Homeomorph.apply_symm_apply] using
    presRoseDiskAttaching_link w b j ((b j).symm y)

/-- Both the cone attachment and the mapping-cylinder collapse are actual
maps; this equivalence has no unproved CW-model comparison as an input. -/
def presRealizationRoseDiskHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (PresPos w))
      (DiskAttachment (presRoseDiskAttaching w b)) := by
  letI := fun j => relatorCircle_nonempty w j (hw j)
  exact (coneAdjRealizationDiskHomeomorph _ _
    (relatorCircleOrderIso w) b).toHomotopyEquiv.trans
      (diskAttachmentBaseChangeHomotopyEquiv (presCylinderDiskAttaching w b)
        (presOldRoseHomotopyEquiv w))

@[simp] theorem presRealizationRoseDiskHomotopyEquiv_old
    (x : orderNerveRealization (ConeAdjBase _)) :
    presRealizationRoseDiskHomotopyEquiv w hw b (coneAdjRealizationOld (circSet w) x) =
      old _ _
        (presOldRoseHomotopyEquiv w x) := by
  letI := fun j => relatorCircle_nonempty w j (hw j)
  change diskAttachmentBaseChangeHomotopyEquiv _ _
    (coneAdjRealizationDiskHomeomorph _ _ _ _ _) = _
  erw [coneAdjRealizationDiskHomeomorph_old, diskAttachmentBaseChangeHomotopyEquiv_old]
  rfl

end FiniteChains.PresModel
