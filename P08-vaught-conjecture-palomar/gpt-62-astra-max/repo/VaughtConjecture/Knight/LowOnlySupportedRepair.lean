/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyNormalization
public import VaughtConjecture.Knight.CanonicalPairedInverse

/-! # Protected terminal decoding for the gate-free LOW family

This specializes the supported-terminal construction of `ReceivingSupportedRepair`
to the already-proved gate-free fibres. The complete vector includes future fields
and the cutoff. Whole-block collapse is above the protected cut, so even unused
grid endpoints below that cut survive. No physical prefix hypothesis is hidden in
this source-level result; its ladder application is in `LowOnlyLadderRepair`.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly
open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref
open CanonicalPairedInverse
noncomputable section
variable {n K j B : ℕ} {P C : SemScheme n}

namespace Family
variable (F : Family P C K)

/-- Constructed source repair, including protected unused grid endpoints. -/
abbrev ProtectedRepair (a : Field P C → ExtOrd) (s : State P C) (j B : ℕ) := ProfileCatalogue.Repair (profileFamily F j) a s B

theorem exists_protected_repair (hj : 1 ≤ j) {a}
    (ha : a ∈ CanonicalPairedProfiles.inventory (Field P C) j) {S}
    (hS : F.Admissible j S) (hag : CappedEq a S.profile (grid j B)) : Nonempty (F.ProtectedRepair a S j B) :=
  ProfileCatalogue.exists_repair (profileFamily F j) hj ha hS hag

/-- The private fibre constructs admission and agreement before normalization. -/
theorem private_protected_repair (hj : 1 ≤ j) {S}
    (hS : F.Admissible j S)
    (hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j)
    {v}
    (hv : C.rows.Lawful v)
    (hag : CappedEq v (S.lowerC j) (grid j B)) :
    ∃ S', F.Admissible j S' ∧ S'.lowerC j = v ∧
      S.CapEq (grid j B) S' ∧ S.FutureEq j S' ∧
      Nonempty (F.ProtectedRepair S.profile S' j B) := by
  obtain ⟨S', hS', hv', hcap, hfuture⟩ :=
    F.private_lift hS hv ((grid_visible j B).mono (min_le_left _ _)) hag
  exact ⟨S', hS', hv', hcap, hfuture, F.exists_protected_repair hj hcanon hS'
    (fun d => (State.capEq_iff_profile.mp hcap d).symm)⟩

/-- Donor prescription uses the checked release fibre, not a face exchange. -/
theorem donor_protected_repair (hj : 1 ≤ j) {S}
    (hS : F.Admissible j S)
    (hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j)
    {u}
    (hu : P.rows.Lawful u)
    (hag : CappedEq u (S.lowerP j) (grid j B)) :
    ∃ S', F.Admissible j S' ∧ S'.lowerP j = u ∧
      S.CapEq (grid j B) S' ∧ S.FutureEq j S' ∧
      Nonempty (F.ProtectedRepair S.profile S' j B) := by
  obtain ⟨S', hS', hu', hcap, hfuture⟩ :=
    F.donor_lift hS hu ((grid_visible j B).mono (min_le_left _ _)) hag
  exact ⟨S', hS', hu', hcap, hfuture, F.exists_protected_repair hj hcanon hS'
    (fun d => (State.capEq_iff_profile.mp hcap d).symm)⟩

end Family
end
end VaughtConjecture.Knight.LowOnly
