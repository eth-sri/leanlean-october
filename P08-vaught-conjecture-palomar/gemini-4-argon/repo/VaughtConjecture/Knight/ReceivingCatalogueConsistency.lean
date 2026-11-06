/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingCatalogueAvailability

/-! # Consistency of the catalogue-derived fixed receiving carrier

The rows are unchanged. This closes the incidence and availability ledger;
bountifulness, and hence packaging a legal scheme, remain separate.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingCatalogueConsistency
open Transform Value ExtOrd CappedDonor CappedDonor.Ref ReceivingLadderCarrier
open ReceivingCatalogueSources ReceivingCatalogueIncidences ReceivingCatalogueAvailability
noncomputable section

variable {I : Type*} [Fintype I] {nP K : ℕ} {P : SemScheme (nP + 1)}
  {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)
  (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)

local notation "D" => carrier L hC
local notation "E" => semantics L hC request
local notation "T" => SupportLadderRows.Point (rungs (P := P) (C := C))
  (TField P C) (Controller L)

@[simp] theorem row_old (a : Cell C.scheme)
    (d : (D).below ((D).cell (old C.scheme hC a))) :
    (E).E (old C.scheme hC a) d = C.rows.E a (oldArg C.scheme hC a d) :=
  ReceivingLadderSemantics.inherited _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem row_request
    (d : (D).below ((D).cell (added C.scheme hC .request))) :
    (E).E (added C.scheme hC .request) d = SupportLadderRows.source 1 1 := by
  simp only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
    view_added]

@[simp] theorem row_ladder (b : Bool) (v : T)
    (d : (D).below ((D).cell (added C.scheme hC (.ladder b v)))) :
    (E).E (added C.scheme hC (.ladder b v)) d =
      ladderRow C.scheme hC privateField (.field (.req request)) (ranks L) v d.1 := by
  simp only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
    view_added]

@[simp] theorem row_upper (b : Bool) (a : Controller L) (node : Bool)
    (d : (D).below ((D).cell (added C.scheme hC (.upper b a node)))) :
    (E).E (added C.scheme hC (.upper b a node)) d =
      upperRow L hC request a node d.1 := by
  simp only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
    view_added, upperRow]

@[simp] theorem row_apex (d : (D).below ((D).cell (added C.scheme hC .apex))) :
    (E).E (added C.scheme hC .apex) d = ⊥ := by
  simp only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
    view_added]

end
end VaughtConjecture.Knight.ReceivingCatalogueConsistency
