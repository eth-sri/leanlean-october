module

public import RequestProject.PresWordDiskNaturality
public import RequestProject.PresConeBallNaturality

@[expose] public section

/-! Naturality of the entire presentation-to-disk-model comparison.
The proof uses the actual old/cone quotient cover and the actual radial
disk coordinates; no relative-model comparison is assumed. -/

noncomputable section

namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Topology

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}

theorem actualPresWordDiskComparison_cone (hw : ∀ j, w j ≠ []) (j : J)
    (x : orderNerveRealization (Set.Iic (apexOf w j))) :
    actualPresWordDiskComparison w hw (coneAdjRealizationCell (circSet w) ⟨j, x⟩) =
      RelativeAttachment.cell _ _
        ⟨j, presConeBallHomeomorph w j (List.length_pos_of_ne_nil (hw j)) x⟩ := by
  letI := fun j => relatorCircle_nonempty w j (hw j)
  change diskAttachmentBaseChangeHomotopyEquiv _ _
    (coneAdjRealizationDiskHomeomorph _ _ _ _ _) = _
  erw [coneAdjRealizationDiskHomeomorph_cell, diskAttachmentBaseChangeHomotopyEquiv_cell]
  rfl

namespace PresWordEmbedding
variable (h : PresWordEmbedding w v)

def cylinderMap : CylBase w →o CylBase v where
  toFun
    | .inl r => .inl (h.roseMap r)
    | .inr c => .inr (h.circleMap c)
  monotone' := by
    intro p q hpq
    have H := h.posMap.monotone (show (ConeAdj.inc p) ≤ ConeAdj.inc q from hpq)
    cases p <;> cases q <;> exact H

variable (p : CylBase w)

theorem cylinderMap_inc :
    ConeAdj.inc (h.cylinderMap p) = h.posMap (ConeAdj.inc p) := by
  cases p <;> rfl

theorem cylinderRetr_natural :
    cylRetr _ (h.cylinderMap p) = h.roseMap (cylRetr (aHom w) p) := by
  cases p with
  | inl r => rfl
  | inr c => exact h.attaching_map c

def oldPartMap : ConeAdjBase (circSet w) →o ConeAdjBase (circSet v) where
  toFun x := ⟨h.posMap x.val, by
    obtain ⟨p, hp⟩ := x.property
    erw [← hp]
    exact ⟨h.cylinderMap p, h.cylinderMap_inc p⟩⟩
  monotone' := fun _ _ hxy => h.posMap.monotone hxy

theorem oldPartMap_baseOrderIso (x : ConeAdjBase _) :
    coneAdjBaseOrderIso (h.oldPartMap x) = h.cylinderMap (coneAdjBaseOrderIso x) := by
  apply ConeAdj.inc_injective
  erw [h.cylinderMap_inc]
  exact (Classical.choose_spec (h.oldPartMap x).property).trans
    (congrArg h.posMap (Classical.choose_spec x.property)).symm

variable (x : orderNerveRealization (ConeAdjBase (circSet w)))

theorem realization_old_natural :
    orderNerveRealizationMap h.posMap h.posMap.monotone (coneAdjRealizationOld (circSet w) x) =
      coneAdjRealizationOld _
        (orderNerveRealizationMap h.oldPartMap h.oldPartMap.monotone x) := by
  erw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]; rfl

theorem oldRoseCollapse_natural :
    presOldRoseHomotopyEquiv v (orderNerveRealizationMap h.oldPartMap h.oldPartMap.monotone x) =
      orderNerveRealizationMap h.roseMap h.roseMap.monotone (presOldRoseHomotopyEquiv w x) := by
  change orderNerveRealizationMap _ (cylRetr_monotone _)
      (orderNerveRealizationMap (coneAdjBaseOrderIso (S := circSet v))
        (coneAdjBaseOrderIso (S := circSet v)).monotone
        (orderNerveRealizationMap h.oldPartMap h.oldPartMap.monotone x)) =
    orderNerveRealizationMap h.roseMap h.roseMap.monotone
      (orderNerveRealizationMap (cylRetr (aHom w)) (cylRetr_monotone (aHom w))
        (orderNerveRealizationMap (coneAdjBaseOrderIso (S := circSet w))
          (coneAdjBaseOrderIso (S := circSet w)).monotone x))
  simp only [orderNerveRealizationMap_comp]
  have hf : (cylRetr _ ∘ coneAdjBaseOrderIso ∘ h.oldPartMap) =
      (h.roseMap ∘ cylRetr _ ∘ coneAdjBaseOrderIso) := by
    funext p
    simp [h.oldPartMap_baseOrderIso, h.cylinderRetr_natural]
  simp_all

theorem realization_cone_natural (j : J) (x : orderNerveRealization (Set.Iic (apexOf w j))) :
    orderNerveRealizationMap h.posMap h.posMap.monotone (coneAdjRealizationCell (circSet w) ⟨j, x⟩) =
      coneAdjRealizationCell _
        ⟨h.cell j, orderNerveRealizationMap _ (h.coneLowerMap j).monotone x⟩ := by
  erw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]; rfl

variable (hw : ∀ j, w j ≠ []) (hv : ∀ k, v k ≠ [])

theorem actualPresWordDiskComparison_natural (x : orderNerveRealization (PresPos w)) :
    actualPresWordDiskComparison v hv (orderNerveRealizationMap h.posMap h.posMap.monotone x) =
      h.wordDiskMap hw hv (actualPresWordDiskComparison w hw x) := by
  obtain ⟨z, rfl⟩ := (coneAdjRealization_piece_isQuotientMap (circSet w)).surjective x
  cases z with
  | inl x =>
      simp [h.realization_old_natural, actualPresWordDiskComparison_old, h.wordDiskMap_old, h.oldRoseCollapse_natural]
  | inr z =>
      rcases z with ⟨j, x⟩
      erw [h.realization_cone_natural, actualPresWordDiskComparison_cone,
        actualPresWordDiskComparison_cone, h.wordDiskMap_cell, h.presConeBallHomeomorph_natural]

theorem diskRoseBaseChange_natural (x : ActualPresWordDisks w hw) :
    diskAttachmentBaseChangeHomotopyEquiv _
        (orderRoseRealizationHomeomorph B).toHomotopyEquiv (h.wordDiskMap hw hv x) =
      h.classicalWordDiskMap hw hv
        (diskAttachmentBaseChangeHomotopyEquiv (actualPresWordAttaching w hw)
          (orderRoseRealizationHomeomorph A).toHomotopyEquiv x) := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective _
    _ x
  cases z with
  | inl x =>
      exact (congrArg
        _
        (orderRoseRealizationHomeomorph_natural h x)).trans
          (h.classicalWordDiskMap_old hw hv (orderRoseRealizationHomeomorph A x)).symm
  | inr d =>
      erw [h.wordDiskMap_cell, diskAttachmentBaseChangeHomotopyEquiv_cell,
        diskAttachmentBaseChangeHomotopyEquiv_cell]; exact (h.classicalWordDiskMap_cell hw hv d).symm

theorem presClassicalDiskComparison_natural (x : orderNerveRealization (PresPos w)) :
    presClassicalDiskComparison v hv (orderNerveRealizationMap h.posMap h.posMap.monotone x) =
      h.classicalWordDiskMap hw hv (presClassicalDiskComparison w hw x) := by
  change diskAttachmentBaseChangeHomotopyEquiv _ _
    (actualPresWordDiskComparison v hv _) = _
  erw [h.actualPresWordDiskComparison_natural hw hv, h.diskRoseBaseChange_natural hw hv]
  rfl

theorem classicalWordDiskMap_killsPi2_iff :
    Whitehead.KillsPi2 (h.classicalWordDiskMap hw hv) ↔
      Whitehead.KillsPi2 (orderNerveRealizationMap h.posMap h.posMap.monotone).hom := by
  apply Whitehead.killsPi2_homotopyEquiv_square_iff
    (presClassicalDiskComparison w hw) (presClassicalDiskComparison v hv)
  have hs : (h.classicalWordDiskMap hw hv).comp (presClassicalDiskComparison w hw).toFun =
      (presClassicalDiskComparison v hv).toFun.comp
        (orderNerveRealizationMap h.posMap h.posMap.monotone).hom := by
    apply ContinuousMap.ext
    exact fun x => (h.presClassicalDiskComparison_natural hw hv x).symm
  aesop

end PresWordEmbedding
end FiniteChains.PresModel
