/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlySupportedRepair
public import VaughtConjecture.Knight.RelativeLadderRankRendering

/-! # LOW repairs retain the entire padded ladder prefix

The fixed index set is the full canonical admitted catalogue at the chosen birth
grade. Replacement membership is constructed by the existing LOW fibres and the
protected inverse. The installed rank rows are not changed or filtered by a
lifting request. All coordinates, including unused and foreign rungs, use the
same external ceiling before and after repair.

This proves physical source receipts, not extraction from an arbitrary ambient
or unrestricted lifting on a higher LOW tower. It does not promote birth-grade
profiles to higher-grade admission.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly.Family
open Transform Value ExtOrd AmalgamationPlan CappedDonor CanonicalPairedInverse
open RelativeLadderLayer
noncomputable section
variable {n K j B : ℕ} {P C : SemScheme n} (F : Family P C K)

abbrev Anchor (j) := ProfileCatalogue.Member (profileFamily F j)

instance (j) : Fintype (F.Anchor j) := ProfileCatalogue.memberFintype (profileFamily F j)

def fields (j : ℕ) (a : F.Anchor j) : Field P C → ExtOrd := a.val

variable {F}

def ProtectedRepair.anchor {a : Field P C → ExtOrd} {S : State P C}
    (r : F.ProtectedRepair a S j B) : F.Anchor j :=
  r.member _

end
end VaughtConjecture.Knight.LowOnly.Family
