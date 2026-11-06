/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.GrowthReplicatedBountiful
import VaughtConjecture.Knight.LowOnlyPaddedLegal

/-! # The legal full-height replicated growth scheme

Coding, consistency and completeness of the installed rows compose with the
constructed all-grade bountifulness theorem. Both original inputs are literal
ordered semantic restrictions, including their rows and occurrence maps.
The generic ordered-face equality lemma is reused from `LowOnlyPaddedLegal`;
no LOW carrier or lifting theorem is used to supply growth bountifulness.

Stage-bounded selected displays and model receiving remain separate.
-/

namespace VaughtConjecture.Knight.GrowthReplicatedLegal
open    AmalgamationPlan Growth
noncomputable section
variable {l m n J : ℕ} {B C : FiniteScope l}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily (Fin l)}
  (I : WholeDonorBoundary.Input Finset.univ B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ (Finset.univ : FiniteScope l).card)
  (hB : B ⊂ Finset.univ) (hC : C ⊂ Finset.univ)
  (hsmall : n + 1 < X.req.N)

/-- The actual full-height replicated carrier, with no assumed output lift. -/
def semScheme : SemScheme l where
  scheme := GrowthHigherMixed.carrier I X T hA hB hC
    ((Finset.univ : FiniteScope l).card - 2) (by omega)
  rows := GrowthHigherMixed.rows I X T hA hB hC
    ((Finset.univ : FiniteScope l).card - 2) (by omega)
  rows_coded := GrowthReplicatedRows.build_coded I X T hA hB hC _ _
  consistent := GrowthReplicatedRows.build_consistent I X T hA hB hC _ _
  bountiful := GrowthReplicatedBountiful.bountiful I X T hA hB hC hsmall
  complete := GrowthReplicatedRows.complete

local notation "E" => semScheme I X T hA hB hC hsmall

theorem plan : (E).scheme.plan = R :=
  GrowthPaddedIteration.build_plan I X T hA hB hC

def donor : ExactSemanticFace I.leftRows (E).rows :=
  GrowthReplicatedRows.donorFace I X T hA hB hC _ _

def privateFace : ExactSemanticFace I.rightRows (E).rows :=
  GrowthReplicatedRows.privateFace I X T hA hB hC _ _

theorem donor_plan : Plan.restrictPlan (E).scheme.plan B =
    I.left.scheme.plan.image (Finset.image I.placeLeft) := by
  rw [plan]; exact I.planLeft

theorem private_plan : Plan.restrictPlan (E).scheme.plan C =
    I.right.scheme.plan.image (Finset.image I.placeRight) := by
  rw [plan]; exact I.planRight

local notation "donor_plan₀" => donor_plan I X T hA hB hC hsmall

def donor_visible :=
  OrderedFaceRestriction.visible I.left (E).scheme I.placeLeft I.imageLeft
    (donor_plan₀)

local notation "private_plan₀" => private_plan I X T hA hB hC hsmall

def private_visible :=
  OrderedFaceRestriction.visible I.right (E).scheme I.placeRight I.imageRight
    (private_plan₀)

/-- Literal donor equality, including its semantic rows and occurrence order. -/
theorem restrict_donor :
    (E).restrictFace I.placeLeft (donor_visible I X T hA hB hC hsmall) = I.left :=
  LowOnlyPaddedLegal.restrict_eq_of_face (GrowthReplicatedRows.donor_order I X T hA hB hC _ _)
    (donor_plan₀)

/-- Literal private equality; no merely semantic-equivalence substitute. -/
theorem restrict_private :
    (E).restrictFace I.placeRight (private_visible I X T hA hB hC hsmall) = I.right :=
  LowOnlyPaddedLegal.restrict_eq_of_face (GrowthReplicatedRows.private_order I X T hA hB hC _ _)
    (private_plan₀)

theorem donor_occurrence d :
    CellScheme.restrictFace.toCell (E).scheme I.placeLeft
      (donor_visible I X T hA hB hC hsmall)
      (Fin.cast (congrArg (fun D => D.scheme.card)
        (restrict_donor I X T hA hB hC hsmall)).symm d) =
      (donor I X T hA hB hC hsmall).map d :=
  OrderedFaceRestriction.toCell_eq I.left (E).scheme (E).rows I.placeLeft I.imageLeft
    (donor I X T hA hB hC hsmall) (GrowthReplicatedRows.donor_order I X T hA hB hC _ _)
    (donor_plan₀) d

theorem private_occurrence d :
    CellScheme.restrictFace.toCell (E).scheme I.placeRight
      (private_visible I X T hA hB hC hsmall)
      (Fin.cast (congrArg (fun D => D.scheme.card)
        (restrict_private I X T hA hB hC hsmall)).symm d) =
      (privateFace I X T hA hB hC hsmall).map d :=
  OrderedFaceRestriction.toCell_eq I.right (E).scheme (E).rows I.placeRight I.imageRight
    (privateFace I X T hA hB hC hsmall) (GrowthReplicatedRows.private_order I X T hA hB hC _ _)
    (private_plan₀) d

