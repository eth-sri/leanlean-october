/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingGradeOnePhysicalChart
public import VaughtConjecture.Knight.SameScopeBountiful

set_option linter.privateModule false

/-! # Lower private prescriptions inserted into the installed catalogue

At a grade-two-visible source-grid cut, a lawful private grade-one prescription
has a constructed grade-two old extension. The grade-two fibre and supported
insertion then produce an actual installed controller, exact lower field
readback, and the entire physical rank prefix. This is not upward admission of
an arbitrary grade-one state: every other field may be repaired above the cut.

The source-grid cap concerns the underlying grade-two field profile, not the
physical rank-coded row or its external agreement cap. Deriving this input from
an arbitrary active physical lifting query remains a separate obligation.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingLowerCatalogueInsertion
open Transform Value ExtOrd CappedDonor CappedDonor.Ref ReceivingLadderCarrier
open ReceivingCatalogueSources CanonicalPairedInverse ReceivingSupportedRepair
noncomputable section

variable {I : Type*} [Fintype I] {nP K : ℕ} {P : SemScheme (nP + 1)}
  {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)

variable (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)
local notation "D" => carrier L hC
local notation "ℓ" => rungs (P := P) (C := C)

end
end VaughtConjecture.Knight.ReceivingLowerCatalogueInsertion
