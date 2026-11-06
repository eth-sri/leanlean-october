/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveActiveLift
public import VaughtConjecture.Knight.CanonicalRecursiveTopSections

/-! # All-cap proper-face lifting at the recursive successor grade

Bottom-cap supply first completes the actual old boundary using its two
lifting clauses, then extends through the recursive layers with exact top
decoding. Positive caps split into active and inactive prescribed owners.
No future completion or output bountifulness is assumed.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalRecursiveFullLift
open Transform Value ExtOrd CoatomBoundaryExtension CanonicalRecursiveSuccessorRows CanonicalRecursiveCutPrefix CanonicalRecursiveActiveLift

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)
  {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A)
  {U V O : Finset ι × ℕ}
  (hcover : ∀ d : Cell (cut (D := D) n),
  GradedLe ((cut (D := D) n).cell d) U ∨ GradedLe ((cut (D := D) n).cell d) V)
  (hCU : GradedLe (C, n + 4) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
  (hinter : ∀ d : Cell (cut (D := D) n), GradedLe ((cut (D := D) n).cell d) U →
  GradedLe ((cut (D := D) n).cell d) V → GradedLe ((cut (D := D) n).cell d) O)
  (hleft : CappedLift (cutRows sem n) hCU) (hright : CappedLift (cutRows sem n) hOV)

include hC hCA hcover hOU hinter hleft hright in
theorem full_lift
    (hb : CanonicalRecursiveRestoration.LowerBountiful sem n hA (predecessorState sem n hA hp))
    (hCc : n + 4 ≤ C.card)
    (hfull : ∃ c : (cut (D := D) n).below (C, n + 4),
      (cut (D := D) n).cell c.1 = (C, n + 4))
    (hU : U.2 ≤ n + 4) (hV : V.2 ≤ n + 4) :
    CappedLift (outputRows sem n hA hp)
      (show GradedLe (C, n + 4) (A, n + 4) from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  have hCnot : ¬ A ⊆ C := fun h => hCA (Finset.Subset.antisymm (D.isPlan.subset_of_mem hC) h)
  exact SingleFaceTailRestoration.full_lift_of_owner (D.isPlan.subset_of_mem hC)
    (CanonicalRecursiveRestoration.lower_clause sem n hA hp (predecessorState sem n hA hp)
      hb hC (Nat.le_of_succ_le hCc))
    (CanonicalRecursiveTopSections.faceEquiv sem (n + 1) hA (C, n + 4) hCnot le_rfl)
    (oldTarget sem n hA)
    (CanonicalRecursiveTopSections.faceEquiv_val sem (n + 1) hA (C, n + 4) hCnot le_rfl)
    (oldTarget_cell sem n hA)
    (CanonicalRecursiveTopSections.pullback_respects sem hp (n + 1) hA (C, n + 4) hCnot le_rfl)
    (CanonicalRecursiveTopSections.exists_local_section sem hp (n + 1) hA hC hCA
      hcover hCU hOU hOV hinter hleft hright)
    hCU hleft hfull fun c hc _ hpr _ hqr _ hγ hγb hag hpc _ hl =>
      CanonicalRecursiveOwnerLift.exists_owner_capped_lift sem n hA hp
        (predecessorState sem n hA hp) c hc hpr hqr hγ hγb hag hpc
        hcover _ hOU hOV hinter hl hright hU hV
