/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlySupportedRepair
public import VaughtConjecture.Knight.RelativeLadderRankRendering
public import VaughtConjecture.Knight.OrbitPrefixSupport

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly.Family

open Transform Value ExtOrd AmalgamationPlan CappedDonor CanonicalPairedInverse

open RelativeLadderLayer

noncomputable section

variable {n K j : ℕ} {P C : SemScheme n} (F : Family P C K)

@[implicit_reducible]
def catalogue (j : ℕ) :=
  CanonicalPairedProfiles.Realized (Field P C) j State.profile (F.Admissible j)

theorem catalogue_finite (j : ℕ) : (F.catalogue j).Finite :=
  CanonicalPairedProfiles.realized_finite _ _ _ _

abbrev Anchor (j : ℕ) := {a // a ∈ F.catalogue j}

instance (j : ℕ) : Fintype (F.Anchor j) := (F.catalogue_finite j).fintype

def fields (j : ℕ) (a : F.Anchor j) : Field P C → ExtOrd := a.val

end

end VaughtConjecture.Knight.LowOnly.Family
