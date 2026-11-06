/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.LowOnlySupportedRepair
import VaughtConjecture.Knight.RelativeLadderRankRendering
import VaughtConjecture.Knight.OrbitPrefixSupport

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

namespace VaughtConjecture.Knight.LowOnly.Family


noncomputable section
variable {n K j B : ℕ} {P C : SemScheme n} (F : Family P C K)

def catalogue j :=
  {a | a ∈ CanonicalPairedProfiles.inventory (Field P C) j ∧
    ∃ S , F.Admissible j S ∧ S.profile = a}

theorem catalogue_finite j : (F.catalogue j).Finite :=
  (CanonicalPairedProfiles.inventory_finite (Field P C) j).subset (fun _ h => h.1)

abbrev Anchor j := {a // a ∈ F.catalogue j}

instance (j : ℕ) : Fintype (F.Anchor j) := (F.catalogue_finite j).fintype

def fields j (a : F.Anchor j) := a.val

variable {F}

def ProtectedRepair.anchor {a} {S}
    (r : F.ProtectedRepair a S j B) : F.Anchor j :=
  ⟨r.encoded.profile, r.canonical, r.encoded, r.admitted, rfl⟩

