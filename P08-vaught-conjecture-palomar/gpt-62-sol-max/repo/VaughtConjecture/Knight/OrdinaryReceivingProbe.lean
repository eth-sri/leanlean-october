/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryReceivingAssembly

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryReceivingProbe

open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref

open OrdinaryReceivingAssembly

noncomputable section

variable {I : Type*} [Fintype I] {nP n : ℕ}

variable {B T : Finset (Fin (n + 5))} {plan : Finset (Finset (Fin (n + 5)))}

variable (W : WholeDonorBoundary.Input Finset.univ B T plan nP (n + 4) (nP + 1))

variable (R : Ref I nP (n + 4) (n + 4) W.right W.left)

variable (hunion : (Finset.univ : Finset (Fin (n + 5))) = B ∪ T)

variable (hface : ∀ i : Cell W.common.scheme,
  ∃ d : W.right.scheme.below (R.A, R.KA),
    d.1 = W.shared.g i ∧ (R.face d).1 = W.shared.f i)

abbrev privateFace : ExactSemanticFace W.leftRows (semScheme W R hunion hface).rows :=
  OrdinaryFinalInstallation.originalFace R (input W R hunion hface)
    (predecessor W R hunion).grade_bound W.left W.placeLeft W.imageLeft (private_ne W)
    (predecessor W R hunion).leftFace

abbrev requestFace : ExactSemanticFace W.rightRows (semScheme W R hunion hface).rows :=
  OrdinaryFinalInstallation.originalFace R (input W R hunion hface)
    (predecessor W R hunion).grade_bound W.right W.placeRight W.imageRight (request_ne W R)
    (predecessor W R hunion).rightFace

theorem private_order : StrictMono (privateFace W R hunion hface).map :=
  OrdinaryFinalInstallation.originalFace_order R (input W R hunion hface)
    (predecessor W R hunion).grade_bound W.left W.placeLeft W.imageLeft (private_ne W)
    (predecessor W R hunion).leftFace (predecessor W R hunion).left_order

theorem request_order : StrictMono (requestFace W R hunion hface).map :=
  OrdinaryFinalInstallation.originalFace_order R (input W R hunion hface)
    (predecessor W R hunion).grade_bound W.right W.placeRight W.imageRight (request_ne W R)
    (predecessor W R hunion).rightFace (predecessor W R hunion).right_order

private theorem carrier_plan : (semScheme W R hunion hface).scheme.plan = plan :=
  (predecessor W R hunion).plan

theorem private_receipt : OrderedFaceRestriction.Receipt W.left (semScheme W R hunion hface)
    W.placeLeft (privateFace W R hunion hface).map :=
  W.left_receipt (carrier_plan W R hunion hface) _ (private_order W R hunion hface)

theorem request_receipt : OrderedFaceRestriction.Receipt W.right (semScheme W R hunion hface)
    W.placeRight (requestFace W R hunion hface).map :=
  W.right_receipt (carrier_plan W R hunion hface) _ (request_order W R hunion hface)

abbrev gate (a : OrdinaryFinalCatalogue.Member R) :
    Cell (semScheme W R hunion hface).scheme :=
  OrdinaryFinalInstallation.marked R (input W R hunion hface) a

abbrev apex : Cell (semScheme W R hunion hface).scheme :=
  FinalGateApex.apex (input W R hunion hface) (Finset.card_fin _)

theorem gate_grade (a : OrdinaryFinalCatalogue.Member R) :
    (semScheme W R hunion hface).scheme.grade (gate W R hunion hface a) = n + 4 := by
  exact congrArg Prod.snd
    ((FinalGateApex.old_index (input W R hunion hface) (Finset.card_fin _)
      ((input W R hunion hface).added a true)).trans
        ((input W R hunion hface).added_index a true))

/-- The model's bottom-pattern test needs a lawful raw display, not a stage type. -/
theorem exists_raw_display :
    ∃ (a : OrdinaryFinalCatalogue.Member R) (r : Cell (semScheme W R hunion hface).scheme → ExtOrd),
      RespectsSemantics (semScheme W R hunion hface).rows r ∧
      (∀ d, r ((requestFace W R hunion hface).map d) = R.p d) ∧
      (∀ d, r ((privateFace W R hunion hface).map d) = R.vact d) ∧
      r (gate W R hunion hface a) = ⊤ ∧ r (apex W R hunion hface) = ⊥ :=
  OrdinaryFinalInstallation.exists_installed_raw_display R (input W R hunion hface)
    (predecessor W R hunion).grade_bound (fun _ _ => rfl) rfl
    (fun _ hz => CanonicalFieldLayer.grid_short _ _ hz)
    (fun a d _ => lower_support W R hunion hface a d) (owners W R hunion hface)
    (predecessor W R hunion).rightFace.map (predecessor W R hunion).leftFace.map
    (lower_request W R hunion hface) (lower_private W R hunion hface)

/-- Arbitrary lawful physical sections: no chart, admission, synchronization
or selected-family coverage is supplied by the caller. -/
theorem capped_readback {q : Cell (semScheme W R hunion hface).scheme → ExtOrd}
    (hq : RespectsSemantics (semScheme W R hunion hface).rows q)
    (hretain : ∀ d, q ((privateFace W R hunion hface).map d) = R.vact d)
    (a : OrdinaryFinalCatalogue.Member R) (hgate : q (gate W R hunion hface a) ≠ ⊥)
    (d : Cell W.right.scheme) :
    min (q ((requestFace W R hunion hface).map d)) (R.cut R.vactL) =
      min (R.p d) (R.cut R.vactL) :=
  OrdinaryFinalInstallation.capped_readback R (input W R hunion hface)
    (by grind) (fun _ _ => rfl) rfl
    (predecessor W R hunion).rightFace.map (predecessor W R hunion).leftFace.map
    (fun d => congrArg Prod.snd ((predecessor W R hunion).rightFace.index d))
    (fun d => congrArg Prod.snd ((predecessor W R hunion).leftFace.index d))
    (lower_request W R hunion hface) (lower_private W R hunion hface) hq hretain a hgate d

theorem readback_below {q : Cell (semScheme W R hunion hface).scheme → ExtOrd}
    (hq : RespectsSemantics (semScheme W R hunion hface).rows q)
    (hretain : ∀ d, q ((privateFace W R hunion hface).map d) = R.vact d)
    (a : OrdinaryFinalCatalogue.Member R) (hgate : q (gate W R hunion hface a) ≠ ⊥)
    {δ : ExtOrd} (hδ : δ ≤ R.cut R.vactL) (d : Cell W.right.scheme) :
    min (q ((requestFace W R hunion hface).map d)) δ = min (R.p d) δ :=
  GradeTailRestoration.cap_below (by solve_by_elim [capped_readback]) hδ

end

end VaughtConjecture.Knight.OrdinaryReceivingProbe
