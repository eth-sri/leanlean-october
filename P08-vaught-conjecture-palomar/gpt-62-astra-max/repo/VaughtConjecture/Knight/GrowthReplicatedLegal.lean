/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthReplicatedBountiful
public import VaughtConjecture.Knight.LowOnlyPaddedLegal

/-! # The legal full-height replicated growth scheme

Coding, consistency and completeness of the installed rows compose with the
constructed all-grade bountifulness theorem. Both original inputs are literal
ordered semantic restrictions, including their rows and occurrence maps.
The generic ordered-face equality lemma is reused from `LowOnlyPaddedLegal`;
no LOW carrier or lifting theorem is used to supply growth bountifulness.

Stage-bounded selected displays and model receiving remain separate.
-/

@[expose] public section

namespace VaughtConjecture.Knight.GrowthReplicatedLegal
open Transform Value ExtOrd AmalgamationPlan Growth
noncomputable section
variable {l m n J : ℕ} {B C : Finset (Fin l)}
  {R : Finset (Finset (Fin l))}
  (I : WholeDonorBoundary.Input Finset.univ B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.Attachment X)
  (hA : 2 ≤ (Finset.univ : Finset (Fin l)).card)
  (hB : B ⊂ Finset.univ) (hC : C ⊂ Finset.univ)
  (hsmall : n + 1 < X.req.N)

/-- The actual full-height replicated carrier, with no assumed output lift. -/
def semScheme : SemScheme l where
  scheme := GrowthHigherMixed.carrier (⟨T, hA, hB, hC⟩ : I.GrowthFrame X)
    ((Finset.univ : Finset (Fin l)).card - 2) (by omega)
  rows := GrowthHigherMixed.rows (⟨T, hA, hB, hC⟩ : I.GrowthFrame X)
    ((Finset.univ : Finset (Fin l)).card - 2) (by omega)
  rows_coded := GrowthReplicatedRows.build_coded (⟨T, hA, hB, hC⟩ : I.GrowthFrame X) _ _
  consistent := GrowthReplicatedRows.build_consistent (⟨T, hA, hB, hC⟩ : I.GrowthFrame X) _ _
  bountiful := GrowthReplicatedBountiful.bountiful (⟨T, hA, hB, hC⟩ : I.GrowthFrame X) hsmall
  complete := GrowthReplicatedRows.complete

local notation "E" => semScheme I X T hA hB hC hsmall

theorem plan : (E).scheme.plan = R :=
  GrowthPaddedIteration.build_plan (⟨T, hA, hB, hC⟩ : I.GrowthFrame X) ((Finset.univ : Finset (Fin l)).card - 2) (by omega)

def donor : ExactSemanticFace I.leftRows (E).rows :=
  GrowthReplicatedRows.donorFace (⟨T, hA, hB, hC⟩ : I.GrowthFrame X) _ _

def privateFace : ExactSemanticFace I.rightRows (E).rows :=
  GrowthReplicatedRows.privateFace (⟨T, hA, hB, hC⟩ : I.GrowthFrame X) _ _

theorem donor_plan : Plan.restrictPlan (E).scheme.plan B =
    I.left.scheme.plan.image (Finset.image I.placeLeft) := by
  rw [plan]; exact I.planLeft

theorem private_plan : Plan.restrictPlan (E).scheme.plan C =
    I.right.scheme.plan.image (Finset.image I.placeRight) := by
  rw [plan]; exact I.planRight

theorem donor_visible : Finset.univ.image I.placeLeft ∈ (E).scheme.plan :=
  OrderedFaceRestriction.visible I.left (E).scheme I.placeLeft I.imageLeft
    (donor_plan I X T hA hB hC hsmall)

theorem private_visible : Finset.univ.image I.placeRight ∈ (E).scheme.plan :=
  OrderedFaceRestriction.visible I.right (E).scheme I.placeRight I.imageRight
    (private_plan I X T hA hB hC hsmall)

/-- Literal donor equality, including its semantic rows and occurrence order. -/
theorem restrict_donor :
    (E).restrictFace I.placeLeft (donor_visible I X T hA hB hC hsmall) = I.left :=
  LowOnlyPaddedLegal.restrict_eq_of_face I.left (E) I.placeLeft I.imageLeft
    (donor I X T hA hB hC hsmall) (GrowthReplicatedRows.donor_order (⟨T, hA, hB, hC⟩ : I.GrowthFrame X) _ _)
    (donor_plan I X T hA hB hC hsmall)

/-- Literal private equality; no merely semantic-equivalence substitute. -/
theorem restrict_private :
    (E).restrictFace I.placeRight (private_visible I X T hA hB hC hsmall) = I.right :=
  LowOnlyPaddedLegal.restrict_eq_of_face I.right (E) I.placeRight I.imageRight
    (privateFace I X T hA hB hC hsmall) (GrowthReplicatedRows.private_order (⟨T, hA, hB, hC⟩ : I.GrowthFrame X) _ _)
    (private_plan I X T hA hB hC hsmall)

theorem donor_occurrence d :
    CellScheme.restrictFace.toCell (E).scheme I.placeLeft
      (donor_visible I X T hA hB hC hsmall)
      (Fin.cast (congrArg (fun D : SemScheme (n + 1) => D.scheme.card)
        (restrict_donor I X T hA hB hC hsmall)).symm d) =
      (donor I X T hA hB hC hsmall).map d :=
  OrderedFaceRestriction.toCell_eq I.left (E).scheme (E).rows I.placeLeft I.imageLeft
    (donor I X T hA hB hC hsmall) (GrowthReplicatedRows.donor_order (⟨T, hA, hB, hC⟩ : I.GrowthFrame X) _ _)
    (donor_plan I X T hA hB hC hsmall) d

theorem private_occurrence d :
    CellScheme.restrictFace.toCell (E).scheme I.placeRight
      (private_visible I X T hA hB hC hsmall)
      (Fin.cast (congrArg (fun D : SemScheme J => D.scheme.card)
        (restrict_private I X T hA hB hC hsmall)).symm d) =
      (privateFace I X T hA hB hC hsmall).map d :=
  OrderedFaceRestriction.toCell_eq I.right (E).scheme (E).rows I.placeRight I.imageRight
    (privateFace I X T hA hB hC hsmall) (GrowthReplicatedRows.private_order (⟨T, hA, hB, hC⟩ : I.GrowthFrame X) _ _)
    (private_plan I X T hA hB hC hsmall) d

end
end VaughtConjecture.Knight.GrowthReplicatedLegal
