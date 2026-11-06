/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.LowOnlyPaddedLiftingInduction
import VaughtConjecture.Knight.LowOnlyPaddedEndpoints
import VaughtConjecture.Knight.OrderedFaceRestriction

/-! # The legal full-height padded LOW scheme

Integration's unchanged coding, ordered faces and whole displays compose with
the closed all-cap induction. Both inputs are literal semantic restrictions,
with their actual occurrence order and every row retained. Scope coverage is
derived for the intended two-coface plan, not asserted for extra mixed scopes.

This packages finite legality and admitted selected sections. It does not
assert stage bounds, separator realization or an exact receiving theorem.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedLegal
open    AmalgamationPlan LowOnly
open LowOnlyPaddedIteration LowOnlyPaddedInstallation
noncomputable section

/-- An ordered exact face of a legal output is the literal semantic restriction. -/
theorem restrict_eq_of_face {a b : ℕ} {D : SemScheme a} {E : SemScheme b}
    {f : Fin a ↪ Fin b} {T : FiniteScope b} {hf : Finset.univ.image f = T}
    {G : ExactSemanticFace (PointImageSemantics.rows hf D.rows) E.rows}
    (hm : StrictMono G.map)
    (hp : Plan.restrictPlan E.scheme.plan T = D.scheme.plan.image (Finset.image f)) :
    E.restrictFace f (OrderedFaceRestriction.visible D E.scheme f hf hp) = D := by
  have he := OrderedFaceRestriction.scheme_eq hm hp
  refine SemScheme.ext_of_components (congrArg CellScheme.plan he)
    (congrArg CellScheme.card he) (CellScheme.cell_cast_of_eq he) ?_
  exact OrderedFaceRestriction.row_eq D E.scheme E.rows f hf G hm hp

variable {l m n K : ℕ} {B C : FiniteScope l}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily (Fin l)}
  (I : WholeDonorBoundary.Input Finset.univ B C R m n n)
  (F : LowOnly.Family I.left I.right K)
  (hroot : F.root.Covers I.shared.f I.shared.g)
  (hA : 2 ≤ (Finset.univ : FiniteScope l).card)
  (hB : B ⊂ Finset.univ) (hC : C ⊂ Finset.univ)
  (hcover : ∀ S ∈ R, S ≠ Finset.univ → S ⊆ B ∨ S ⊆ C)

/-- The actual completed carrier, with no supplied output lifting premise. -/
def semScheme : SemScheme l where
  scheme := (build I F hroot hA hB hC
    ((Finset.univ : FiniteScope l).card - 2) (by omega)).carrier
  rows := (build I F hroot hA hB hC
    ((Finset.univ : FiniteScope l).card - 2) (by omega)).rows
  rows_coded := build_coded I F hroot hA hB hC _ _
  consistent := build_consistent I F hroot hA hB hC _ _
  bountiful := LowOnlyPaddedLiftingInduction.full_bountiful I F hroot hA hB hC hcover
  complete := LowOnlyPaddedLiftingInduction.full_complete I F hroot hA hB hC hcover

local notation "E" => semScheme I F hroot hA hB hC hcover

theorem plan : (E).scheme.plan = R := build_plan I F hroot hA hB hC _ _

def donor : ExactSemanticFace I.leftRows (E).rows :=
  donorFace I F hroot hA hB hC _ _

def privateFace : ExactSemanticFace I.rightRows (E).rows :=
  LowOnlyPaddedInstallation.privateFace I F hroot hA hB hC _ _

theorem donor_plan : Plan.restrictPlan (E).scheme.plan B =
    I.left.scheme.plan.image (Finset.image I.placeLeft) := by
  rw [plan]; exact I.planLeft

theorem private_plan : Plan.restrictPlan (E).scheme.plan C =
    I.right.scheme.plan.image (Finset.image I.placeRight) := by
  rw [plan]; exact I.planRight

local notation "donor_plan₀" => donor_plan I F hroot hA hB hC hcover

def donor_visible :=
  OrderedFaceRestriction.visible I.left (E).scheme I.placeLeft I.imageLeft
    (donor_plan₀)

local notation "private_plan₀" => private_plan I F hroot hA hB hC hcover

def private_visible :=
  OrderedFaceRestriction.visible I.right (E).scheme I.placeRight I.imageRight
    (private_plan₀)

local notation "donor₀" => donor I F hroot hA hB hC hcover

/-- Literal equality includes row data, not just a lower-domain equivalence. -/
theorem restrict_donor :
    (E).restrictFace I.placeLeft (donor_visible I F hroot hA hB hC hcover) = I.left :=
  restrict_eq_of_face (donor_order I F hroot hA hB hC _ _)
    (donor_plan₀)

local notation "privateFace₀" => privateFace I F hroot hA hB hC hcover

theorem restrict_private :
    (E).restrictFace I.placeRight (private_visible I F hroot hA hB hC hcover) = I.right :=
  restrict_eq_of_face (private_order I F hroot hA hB hC _ _)
    (private_plan₀)

/-- The restriction's canonical enumeration is the installed donor map. -/
theorem donor_occurrence d :
    CellScheme.restrictFace.toCell (E).scheme I.placeLeft
      (donor_visible I F hroot hA hB hC hcover)
      (Fin.cast (congrArg (fun D => D.scheme.card)
        (restrict_donor I F hroot hA hB hC hcover)).symm d) =
      (donor₀).map d :=
  OrderedFaceRestriction.toCell_eq I.left (E).scheme (E).rows I.placeLeft I.imageLeft
    (donor₀) (donor_order I F hroot hA hB hC _ _)
    (donor_plan₀) d

theorem private_occurrence d :
    CellScheme.restrictFace.toCell (E).scheme I.placeRight
      (private_visible I F hroot hA hB hC hcover)
      (Fin.cast (congrArg (fun D => D.scheme.card)
        (restrict_private I F hroot hA hB hC hcover)).symm d) =
      (privateFace₀).map d :=
  OrderedFaceRestriction.toCell_eq I.right (E).scheme (E).rows I.placeRight I.imageRight
    (privateFace₀) (private_order I F hroot hA hB hC _ _)
    (private_plan₀) d

