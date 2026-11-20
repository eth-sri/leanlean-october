/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingCatalogueIncidences

/-! # Actual mixed-index availability witnesses

The spare terminal rung reaches the reserved ceiling. Parent leaves therefore
dominate every coordinate of a weighted upper row. The witnesses below are
actual occurrences inside the requested lower domain, at either mixed scope.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingCatalogueAvailability
open Transform Value ExtOrd CappedDonor CappedDonor.Ref ReceivingLadderCarrier
open ReceivingCatalogueSources
noncomputable section

variable {I : Type*} [Fintype I] {nP K : ℕ} {P : SemScheme (nP + 1)}
  {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)
  (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)

local notation "D" => carrier L hC
local notation "H" => ReceivingCatalogueSources.ceiling (P := P) (C := C)
local notation "G" => grid (P := P) (C := C)
local notation "T" => SupportLadderRows.Point (rungs (P := P) (C := C))
  (TField P C) (Controller L)

abbrev upperRow (a : Controller L) (node : Bool) : Cell D → ExtOrd :=
  ReceivingLadderUpperRows.row C.scheme hC privateField (.field (.req request))
    (high (R := R)) (ranks L) (fields L) id G H a node

end
end VaughtConjecture.Knight.ReceivingCatalogueAvailability
