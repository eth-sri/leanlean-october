/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLadderBaseCut
public import VaughtConjecture.Knight.ReceivingCatalogueConsistency

set_option linter.privateModule false

/-! # Constructed grade-one charts and low cuts on the receiving catalogue

All source, row and rank hypotheses of the long-ladder cut theorem are
discharged here on the unchanged catalogue-derived carrier. Arbitrary lawful
lower ambients are allowed. Replacement-anchor construction, and consequently
the grade-one scope-raising lift, are not conclusions of this module.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingGradeOnePhysicalChart
open Transform Value ExtOrd CappedDonor CappedDonor.Ref ReceivingLadderCarrier
open ReceivingCatalogueSources SharpWitnessComposition
noncomputable section

variable {I : Type*} [Fintype I] {nP K : ℕ} {P : SemScheme (nP + 1)}
  {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)
  (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)

local notation "D" => carrier L hC
local notation "E" => semantics L hC request
local notation "ℓ" => rungs (P := P) (C := C)

end
end VaughtConjecture.Knight.ReceivingGradeOnePhysicalChart
