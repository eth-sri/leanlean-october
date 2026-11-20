/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLowerCatalogueInsertion

/-! # Visible cuts before invisible canonical fields

An invisible grade-two field starts an orbit slot. The preceding odd slot is
unused, and its endpoint separates exactly the same represented fields. Thus
the source cut need not be obtained by rounding the invisible field upward.
No claim of minimality at unused ordinal points is needed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingGradeOneSourceCut
open Transform Value ExtOrd PairedSlotEncoding
noncomputable section

open CappedDonor CappedDonor.Ref ReceivingLadderCarrier ReceivingCatalogueSources

variable {I : Type*} [Fintype I] {nP K : ℕ} {P : SemScheme (nP + 1)}
  {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)
  (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)

local notation "D" => carrier L hC
local notation "E" => semantics L hC request
local notation "ℓ" => rungs (P := P) (C := C)

local instance : Fintype (C.scheme.below (effC 2 1)) := Fintype.ofFinite _

end
end VaughtConjecture.Knight.ReceivingGradeOneSourceCut
