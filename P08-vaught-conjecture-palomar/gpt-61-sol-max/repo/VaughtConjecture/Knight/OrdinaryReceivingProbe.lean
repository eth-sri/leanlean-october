/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.OrdinaryReceivingAssembly

/-! # The installed ordinary receiving probe and its selected display

Both input semantic schemes are literal ordered restrictions of the constructed
legal carrier. Its selected display retains both inputs, keeps a named grade-N
gate top, and satisfies the stage bound at every auxiliary. Every lawful whole
section retaining the private labels and that gate's positivity reads the
donor back below the actual cut. Model realization is deliberately separate.
-/

namespace VaughtConjecture.Knight.OrdinaryReceivingProbe
open    AmalgamationPlan CappedDonor CappedDonor.Ref
open OrdinaryReceivingAssembly
noncomputable section

variable {I : Type*} [Fintype I] {nP n : ℕ}
variable {B T : Finset (Fin (n + 5))} {plan : Finset (Finset (Fin (n + 5)))}
variable (W : WholeDonorBoundary.Input Finset.univ B T plan nP (n + 4) (nP + 1))
variable (R : Ref I nP (n + 4) (n + 4) W.right W.left)
variable (hunion : (Finset.univ : Finset (Fin (n + 5))) = B ∪ T)
variable (hface : ∀ i ,
  ∃ d ,
    d.1 = W.shared.g i ∧ (R.face d).1 = W.shared.f i)

local notation "input₀" => input W R hunion hface

local notation "predecessor₀" => predecessor W R hunion

local notation "semScheme₀" => semScheme W R hunion hface

abbrev privateFace : ExactSemanticFace W.leftRows (semScheme₀).rows :=
  OrdinaryFinalInstallation.originalFace R (input₀)
    (predecessor₀).grade_bound W.left W.placeLeft W.imageLeft (private_ne W)
    (predecessor₀).leftFace

abbrev requestFace : ExactSemanticFace W.rightRows (semScheme₀).rows :=
  OrdinaryFinalInstallation.originalFace R (input₀)
    (predecessor₀).grade_bound W.right W.placeRight W.imageRight (request_ne W R)
    (predecessor₀).rightFace

local notation "privateFace₀" => privateFace W R hunion hface

theorem private_order : StrictMono (privateFace₀).map :=
  OrdinaryFinalInstallation.originalFace_order R (input₀)
    (predecessor₀).grade_bound W.left W.placeLeft W.imageLeft (private_ne W)
    (predecessor₀).leftFace (predecessor₀).left_order

local notation "requestFace₀" => requestFace W R hunion hface

theorem request_order : StrictMono (requestFace₀).map :=
  OrdinaryFinalInstallation.originalFace_order R (input₀)
    (predecessor₀).grade_bound W.right W.placeRight W.imageRight (request_ne W R)
    (predecessor₀).rightFace (predecessor₀).right_order

theorem private_plan : Plan.restrictPlan (semScheme₀).scheme.plan B =
    W.left.scheme.plan.image (Finset.image W.placeLeft) := by
  change Plan.restrictPlan (predecessor₀).carrier.plan B = _
  rw [(predecessor₀).plan]
  exact W.planLeft

theorem request_plan : Plan.restrictPlan (semScheme₀).scheme.plan T =
    W.right.scheme.plan.image (Finset.image W.placeRight) := by
  change Plan.restrictPlan (predecessor₀).carrier.plan T = _
  rw [(predecessor₀).plan]
  exact W.planRight

def private_visible :=
  OrderedFaceRestriction.visible W.left _ W.placeLeft W.imageLeft
    (private_plan W R hunion hface)

def request_visible :=
  OrderedFaceRestriction.visible W.right _ W.placeRight W.imageRight
    (request_plan W R hunion hface)

/-- Ordered exact semantic faces identify the restriction as a semantic scheme,
including every row, not just its cell inventory. -/
theorem restrict_of_ordered_face {m k : ℕ} (P : SemScheme m) (S : SemScheme k)
    (f : Fin m ↪ Fin k) {U : FiniteScope k} (hf : Finset.univ.image f = U)
    (E : ExactSemanticFace (PointImageSemantics.rows hf P.rows) S.rows)
    (ho : StrictMono E.map)
    (hp : Plan.restrictPlan S.scheme.plan U = P.scheme.plan.image (Finset.image f)) :
    S.restrictFace f (OrderedFaceRestriction.visible P S.scheme f hf hp) = P := by
  have he := OrderedFaceRestriction.scheme_eq ho hp
  refine SemScheme.ext_of_components (congrArg CellScheme.plan he)
    (OrderedFaceRestriction.card_face P S.scheme S.rows f hf E ho hp)
    (fun c => CellScheme.cell_cast_of_eq he c) (fun c d => ?_)
  exact OrderedFaceRestriction.row_eq P S.scheme S.rows f hf E ho hp c d

theorem private_restrict : (semScheme₀).restrictFace W.placeLeft
    (private_visible W R hunion hface) = W.left :=
  restrict_of_ordered_face W.left _ W.placeLeft W.imageLeft (privateFace₀)
    (private_order W R hunion hface) (private_plan W R hunion hface)

theorem request_restrict : (semScheme₀).restrictFace W.placeRight
    (request_visible W R hunion hface) = W.right :=
  restrict_of_ordered_face W.right _ W.placeRight W.imageRight (requestFace₀)
    (request_order W R hunion hface) (request_plan W R hunion hface)

/-- The cell map of the literal private restriction is the installed private map. -/
theorem private_toCell d :
    CellScheme.restrictFace.toCell (semScheme₀).scheme W.placeLeft
      (private_visible W R hunion hface)
      (SemScheme.castCell (private_restrict W R hunion hface).symm d) =
        (privateFace₀).map d :=
  OrderedFaceRestriction.toCell_eq W.left _ _ W.placeLeft W.imageLeft
    (privateFace₀) (private_order W R hunion hface)
    (private_plan W R hunion hface) d

/-- The donor restriction uses the actual installed map, also for noninitial faces. -/
theorem request_toCell d :
    CellScheme.restrictFace.toCell (semScheme₀).scheme W.placeRight
      (request_visible W R hunion hface)
      (SemScheme.castCell (request_restrict W R hunion hface).symm d) =
        (requestFace₀).map d :=
  OrderedFaceRestriction.toCell_eq W.right _ _ W.placeRight W.imageRight
    (requestFace₀) (request_order W R hunion hface)
    (request_plan W R hunion hface) d

abbrev gate (a : OrdinaryFinalCatalogue.Member R) :
    Cell (semScheme₀).scheme :=
  OrdinaryFinalInstallation.marked R (input₀) a

abbrev apex : Cell (semScheme₀).scheme :=
  FinalGateApex.apex (input₀) (Finset.card_fin _)

local notation "gate₀" => gate W R hunion hface

theorem gate_grade a :
    (semScheme₀).scheme.grade (gate₀ a) = n + 4 := congrArg Prod.snd
    ((FinalGateApex.old_index input₀ (Finset.card_fin _)
      ((input₀).added a true)).trans
        ((input₀).added_index a true))

/-- The model's bottom-pattern test needs a lawful raw display, not a stage type. -/
theorem exists_raw_display :
    ∃ a r,
      RespectsSemantics (semScheme₀).rows r ∧
      (∀ d, r ((requestFace₀).map d) = R.p d) ∧
      (∀ d, r ((privateFace₀).map d) = R.vact d) ∧
      r (gate₀ a) = ⊤ ∧ r (apex W R hunion hface) = ⊥ :=
  OrdinaryFinalInstallation.exists_installed_raw_display R (input₀)
    (predecessor₀).grade_bound (fun _ _ => rfl) rfl
    (fun _ hz => CanonicalFieldLayer.grid_short hz)
    (fun a d _ => lower_support W R hunion hface a d) (owners W R hunion hface)
    (predecessor₀).rightFace.map (predecessor₀).leftFace.map
    (lower_request W R hunion hface) (lower_private W R hunion hface)

/-- Arbitrary lawful physical sections: no chart, admission, synchronization
or selected-family coverage is supplied by the caller. -/
theorem capped_readback {q}
    (hq : RespectsSemantics (semScheme₀).rows q)
    (hretain : ∀ d, q ((privateFace₀).map d) = R.vact d)
    a (hgate : q (gate₀ a) ≠ ⊥)
    d :
    min (q ((requestFace₀).map d)) (R.cut R.vactL) =
      min (R.p d) (R.cut R.vactL) :=
  OrdinaryFinalInstallation.capped_readback R (input₀)
    (predecessor₀).grade_bound (fun _ _ => rfl) rfl
    (predecessor₀).rightFace.map (predecessor₀).leftFace.map
    (fun d => congrArg Prod.snd ((predecessor₀).rightFace.index d))
    (fun d => congrArg Prod.snd ((predecessor₀).leftFace.index d))
    (lower_request W R hunion hface) (lower_private W R hunion hface) hq hretain a hgate d

def readback_below {q}
    (hq : RespectsSemantics (semScheme₀).rows q)
    (hretain : ∀ d, q ((privateFace₀).map d) = R.vact d)
    a (hgate : q (gate₀ a) ≠ ⊥)
    {δ} (hδ : δ ≤ R.cut R.vactL) d :=
  GradeTailRestoration.cap_below (capped_readback W R hunion hface hq hretain a hgate d) hδ

