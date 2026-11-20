/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedLiftingInduction
public import VaughtConjecture.Knight.PaddedInstallation
public import VaughtConjecture.Knight.OrderedFaceRestriction

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedLegal

open Transform Value ExtOrd AmalgamationPlan LowOnly

open LowOnlyPaddedIteration

noncomputable section

variable {l m n K : ℕ} {B C : Finset (Fin l)}
  {R : Finset (Finset (Fin l))}
  (I : WholeDonorBoundary.Input Finset.univ B C R m n n)
  (F : LowOnly.Family I.left I.right K)
  (hroot : I.RootMatches F.root)
  (hA : 2 ≤ (Finset.univ : Finset (Fin l)).card)
  (hB : B ⊂ Finset.univ) (hC : C ⊂ Finset.univ)
  (hcover : ∀ S ∈ R, S ≠ Finset.univ → S ⊆ B ∨ S ⊆ C)

local notation "P" => build I F hroot hA hB hC (Finset.card (Finset.univ : Finset (Fin l)) - 2) (by omega)

/-- The actual completed carrier, with no supplied output lifting premise. -/
def semScheme : SemScheme l where
  scheme := (P).carrier
  rows := (P).rows
  rows_coded := Padded.build_coded I.consistent I.coded _ _
  consistent := (P).consistent
  bountiful := LowOnlyPaddedLiftingInduction.full_bountiful I F hroot hA hB hC hcover
  complete := LowOnlyPaddedLiftingInduction.full_complete I F hroot hA hB hC hcover

local notation "E" => semScheme I F hroot hA hB hC hcover

theorem plan : (E).scheme.plan = R := build_plan I F hroot hA hB hC _ _

def donor : ExactSemanticFace I.leftRows (E).rows := (P).face I.leftFace hB.not_ge

def privateFace : ExactSemanticFace I.rightRows (E).rows := (P).face I.rightFace hC.not_ge

theorem donor_receipt :
    OrderedFaceRestriction.Receipt I.left E I.placeLeft (donor I F hroot hA hB hC hcover).map :=
  I.left_receipt (plan I F hroot hA hB hC hcover) _ ((P).face_mono _ hB.not_ge I.left_order)

theorem private_receipt :
    OrderedFaceRestriction.Receipt I.right E I.placeRight (privateFace I F hroot hA hB hC hcover).map :=
  I.right_receipt (plan I F hroot hA hB hC hcover) _ ((P).face_mono _ hC.not_ge I.right_order)

end

end VaughtConjecture.Knight.LowOnlyPaddedLegal
