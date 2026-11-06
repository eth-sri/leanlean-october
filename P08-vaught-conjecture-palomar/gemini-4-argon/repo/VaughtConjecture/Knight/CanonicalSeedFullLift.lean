/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSeedActiveLift
public import VaughtConjecture.Knight.CanonicalRecursiveTopSections

/-! # All-cap proper-face lifting at the recursive seed grade

Bottom-cap supply first completes the actual old boundary using its two
lifting clauses, then extends through the recursive layers with exact top
decoding. Positive caps split into active and inactive prescribed owners.
No future completion or output bountifulness is assumed.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalSeedFullLift
open Transform Value ExtOrd CoatomBoundaryExtension CanonicalRecursiveSeedRows CanonicalSeedCutPrefix CanonicalSeedActiveLift

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hA : 3 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)
  {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A)
  {U V O : Finset ι × ℕ}
  (hcover : ∀ d : Cell (cut (D := D)),
  GradedLe ((cut (D := D)).cell d) U ∨ GradedLe ((cut (D := D)).cell d) V)
  (hCU : GradedLe (C, 3) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
  (hinter : ∀ d : Cell (cut (D := D)), GradedLe ((cut (D := D)).cell d) U →
  GradedLe ((cut (D := D)).cell d) V → GradedLe ((cut (D := D)).cell d) O)
  (hleft : CappedLift (cutRows sem) hCU) (hright : CappedLift (cutRows sem) hOV)

include hC hCA hcover hOU hinter hleft hright in
theorem full_lift
    (hb : CanonicalSeedRestoration.LowerBountiful sem hA hp)
    (hCc : 3 ≤ C.card)
    (hfull : ∃ c : (cut (D := D)).below (C, 3),
      (cut (D := D)).cell c.1 = (C, 3))
    (hU : U.2 ≤ 3) (hV : V.2 ≤ 3) :
    CappedLift (outputRows sem hA hp)
      (show GradedLe (C, 3) (A, 3) from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  have hCnot : ¬ A ⊆ C := fun h => hCA (Finset.Subset.antisymm (D.isPlan.subset_of_mem hC) h)
  exact SingleFaceTailRestoration.full_lift_of_owner (D.isPlan.subset_of_mem hC)
    (CanonicalSeedRestoration.lower_clause sem hA hp hb hC (Nat.le_of_succ_le hCc))
    (CanonicalRecursiveTopSections.faceEquiv sem 0 hA (C, 3) hCnot le_rfl)
    (oldTarget sem hA)
    (CanonicalRecursiveTopSections.faceEquiv_val sem 0 hA (C, 3) hCnot le_rfl)
    (oldTarget_cell sem hA)
    (CanonicalRecursiveTopSections.pullback_respects sem hp 0 hA (C, 3) hCnot le_rfl)
    (CanonicalRecursiveTopSections.exists_local_section sem hp 0 hA hC hCA
      hcover hCU hOU hOV hinter hleft hright)
    hCU hleft hfull fun c hc _ hpr _ hqr _ hγ hγb hag hpc _ hl =>
      CanonicalSeedOwnerLift.exists_owner_capped_lift sem hA hp
        c hc hpr hqr hγ hγb hag hpc hcover _ hOU hOV hinter hl hright hU hV
