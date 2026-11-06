import Mathlib.Tactic

import RequestProject.PresWordDiskNaturality
import RequestProject.PresConeBallNaturality

/-! Naturality of the entire presentation-to-disk-model comparison.
The proof uses the actual old/cone quotient cover and the actual radial
disk coordinates; no relative-model comparison is assumed. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb RelativeAttachment


variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}

theorem actualPresWordDiskComparison_cone (hw : ∀ j, w j ≠ []) (j : J)
    (x : orderNerveRealization (Set.Iic (apexOf w j))) :
    actualPresWordDiskComparison w hw (coneAdjRealizationCell (circSet w) ⟨j, x⟩) =
      RelativeAttachment.cell (actualPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ))
        ⟨j, presConeBallHomeomorph w j (List.length_pos_of_ne_nil (hw j)) x⟩ := by
  letI  := fun j => relatorCircle_nonempty w j (hw j)
  change diskAttachmentBaseChangeHomotopyEquiv _ _
    (coneAdjRealizationDiskHomeomorph _ _ _ _ (coneAdjRealizationCell _ ⟨j, x⟩)) = _
  rw  [coneAdjRealizationDiskHomeomorph_cell, diskAttachmentBaseChangeHomotopyEquiv_cell]
  rfl

namespace PresWordEmbedding
variable (h : PresWordEmbedding w v)

def cylinderMap : CylBase w →o CylBase v where
  toFun
    | .inl r => .inl (h.roseMap r)
    | .inr c => .inr (h.circleMap c)
  monotone' := by
    intro p q hpq
    have H := h.posMap.monotone (show (ConeAdj.inc p : PresPos w) ≤ ConeAdj.inc q from hpq)
    cases p <;> cases q <;> exact H

theorem cylinderMap_inc (p : CylBase w) :
    ConeAdj.inc (h.cylinderMap p) = h.posMap (ConeAdj.inc p) := by
  cases p <;> rfl

theorem cylinderRetr_natural (p : CylBase w) :
    cylRetr (aHom v) (h.cylinderMap p) = h.roseMap (cylRetr (aHom w) p) := by
  cases p with
  | inl r => rfl
  | inr c => exact h.attaching_map c

def oldPartMap : ConeAdjBase (circSet w) →o ConeAdjBase (circSet v) where
  toFun x := ⟨h.posMap x.val, by
    obtain ⟨p, hp⟩ := x.property
    rw  [← hp]
    exact ⟨h.cylinderMap p, h.cylinderMap_inc p⟩⟩
  monotone' := fun _ _ hxy => h.posMap.monotone hxy

theorem oldPartMap_baseOrderIso (x : ConeAdjBase (circSet w)) :
    coneAdjBaseOrderIso (h.oldPartMap x) = h.cylinderMap (coneAdjBaseOrderIso x) := by
  apply ConeAdj.inc_injective (S := circSet v)
  rw  [h.cylinderMap_inc]
  exact (Classical.choose_spec (h.oldPartMap x).property).trans
    (congrArg h.posMap (Classical.choose_spec x.property)).symm

variable (x : orderNerveRealization (ConeAdjBase (circSet w)))
theorem realization_old_natural  :
    orderNerveRealizationMap h.posMap h.posMap.monotone (coneAdjRealizationOld (circSet w) x) =
      coneAdjRealizationOld (circSet v)
        (orderNerveRealizationMap h.oldPartMap h.oldPartMap.monotone x) := by
  
  rw (config := { transparency := .default }) [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  rfl

theorem oldRoseCollapse_natural  :
    presOldRoseHomotopyEquiv v (orderNerveRealizationMap h.oldPartMap h.oldPartMap.monotone x) =
      orderNerveRealizationMap h.roseMap h.roseMap.monotone (presOldRoseHomotopyEquiv w x) := by
  change orderNerveRealizationMap (cylRetr (aHom v)) (cylRetr_monotone (aHom v))
      (orderNerveRealizationMap (coneAdjBaseOrderIso (S := circSet v))
        (coneAdjBaseOrderIso (S := circSet v)).monotone
        (orderNerveRealizationMap h.oldPartMap h.oldPartMap.monotone x)) =
    orderNerveRealizationMap h.roseMap h.roseMap.monotone
      (orderNerveRealizationMap (cylRetr (aHom w)) (cylRetr_monotone (aHom w))
        (orderNerveRealizationMap (coneAdjBaseOrderIso (S := circSet w))
          (coneAdjBaseOrderIso (S := circSet w)).monotone x))
  simp only [orderNerveRealizationMap_comp]
  have hf : (cylRetr (aHom v) ∘ coneAdjBaseOrderIso ∘ h.oldPartMap) =
      (h.roseMap ∘ cylRetr (aHom w) ∘ coneAdjBaseOrderIso) := by
    classical grind [FiniteChains.PresModel.PresWordEmbedding.oldPartMap_baseOrderIso, FiniteChains.PresModel.PresWordEmbedding.cylinderRetr_natural, cylRetr, aHom, coneAdjBaseOrderIso]
  exact orderNerveRealizationMap_congr _ _ hf x

theorem realization_cone_natural (j : J) (x : orderNerveRealization (Set.Iic (apexOf w j))) :
    orderNerveRealizationMap h.posMap h.posMap.monotone (coneAdjRealizationCell (circSet w) ⟨j, x⟩) =
      coneAdjRealizationCell (circSet v)
        ⟨h.cell j, orderNerveRealizationMap (h.coneLowerMap j) (h.coneLowerMap j).monotone x⟩ := by
  
  rw (config := { transparency := .default }) [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  rfl

variable (hw : ∀ j, w j ≠ []) (hv : ∀ k, v k ≠ [])

variable (x : orderNerveRealization (PresPos w))
theorem actualPresWordDiskComparison_natural  :
    actualPresWordDiskComparison v hv (orderNerveRealizationMap h.posMap h.posMap.monotone x) =
      h.wordDiskMap hw hv (actualPresWordDiskComparison w hw x) := by
  obtain ⟨z, rfl⟩ := (coneAdjRealization_piece_isQuotientMap (circSet w)).surjective x
  cases z with
  | inl x =>
      classical grind [FiniteChains.PresModel.PresWordEmbedding.realization_old_natural, FiniteChains.PresModel.actualPresWordDiskComparison_old, FiniteChains.PresModel.PresWordEmbedding.wordDiskMap_old, FiniteChains.PresModel.PresWordEmbedding.oldRoseCollapse_natural, actualPresWordDiskComparison, orderNerveRealizationMap, coneAdjRealizationOld, circSet]
  | inr z =>
      rcases z with ⟨j, x⟩
      change actualPresWordDiskComparison v hv
        (orderNerveRealizationMap h.posMap h.posMap.monotone (coneAdjRealizationCell (circSet w) ⟨j, x⟩)) =
          h.wordDiskMap hw hv (actualPresWordDiskComparison w hw (coneAdjRealizationCell (circSet w) ⟨j, x⟩))
      rw (config := { transparency := .default }) [h.realization_cone_natural, actualPresWordDiskComparison_cone,
        actualPresWordDiskComparison_cone, h.wordDiskMap_cell, h.presConeBallHomeomorph_natural]

theorem diskRoseBaseChange_natural (x : ActualPresWordDisks w hw) :
    diskAttachmentBaseChangeHomotopyEquiv (actualPresWordAttaching v hv)
        (orderRoseRealizationHomeomorph B).toHomotopyEquiv (h.wordDiskMap hw hv x) =
      h.classicalWordDiskMap hw hv
        (diskAttachmentBaseChangeHomotopyEquiv (actualPresWordAttaching w hw)
          (orderRoseRealizationHomeomorph A).toHomotopyEquiv x) := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective (actualPresWordAttaching w hw)
    (boundaryFamilyInclusion J (Fin 2 → ℝ)) x
  cases z with
  | inl x =>
      
      rw (config := { transparency := .default }) [h.wordDiskMap_old, diskAttachmentBaseChangeHomotopyEquiv_old,
        diskAttachmentBaseChangeHomotopyEquiv_old]
      exact (congrArg
        (old (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)))
        (orderRoseRealizationHomeomorph_natural h x)).trans
          (h.classicalWordDiskMap_old hw hv (orderRoseRealizationHomeomorph A x)).symm
  | inr d =>
      
      rw (config := { transparency := .default }) [h.wordDiskMap_cell, diskAttachmentBaseChangeHomotopyEquiv_cell,
        diskAttachmentBaseChangeHomotopyEquiv_cell]
      exact (h.classicalWordDiskMap_cell hw hv d).symm

theorem presClassicalDiskComparison_natural  :
    presClassicalDiskComparison v hv (orderNerveRealizationMap h.posMap h.posMap.monotone x) =
      h.classicalWordDiskMap hw hv (presClassicalDiskComparison w hw x) := by
  change diskAttachmentBaseChangeHomotopyEquiv _ _
    (actualPresWordDiskComparison v hv (orderNerveRealizationMap h.posMap h.posMap.monotone x)) = _
  rw (config := { transparency := .default }) [h.actualPresWordDiskComparison_natural hw hv, h.diskRoseBaseChange_natural hw hv]
  rfl

theorem classicalWordDiskMap_killsPi2_iff :
    Whitehead.KillsPi2 (h.classicalWordDiskMap hw hv) ↔
      Whitehead.KillsPi2 (orderNerveRealizationMap h.posMap h.posMap.monotone).hom := by
  apply Whitehead.killsPi2_homotopyEquiv_square_iff
    (presClassicalDiskComparison w hw) (presClassicalDiskComparison v hv)
  have hs : (h.classicalWordDiskMap hw hv).comp (presClassicalDiskComparison w hw).toFun =
      (presClassicalDiskComparison v hv).toFun.comp
        (orderNerveRealizationMap h.posMap h.posMap.monotone).hom := by
    classical aesop (add simp [FiniteChains.PresModel.PresWordEmbedding.presClassicalDiskComparison_natural])
  rw (config := { transparency := .default }) [hs]

end FiniteChains.PresModel.PresWordEmbedding

