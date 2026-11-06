
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.CanonicalSeedBountiful
import VaughtConjecture.Knight.CanonicalRecursiveRecurrence

/-! # Initialized bountiful grade recursion on the actual canonical rows

Seed lifting is proved directly on its complete persistent inventory. The
banked lower-pair theorem supplies restoration; no equivalence of catalogues
is used to import three-grade bountifulness. The established successor then
iterates from this constructed base, within the explicit old-coatom bounds.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveInitialized
open    CoatomBoundaryExtension AmalgamationPlan
open CanonicalRecursiveRecurrence

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : AvoidsValue D.scope A)
variable (hs : sem.IsConsistent) (hold : CanonicalCoatomBountiful.OldLifts sem)
variable {L R : Finset ι} (hL : L ∈ D.plan) (hR : R ∈ D.plan)
variable (hLA : L ≠ A) (hRA : R ≠ A) (hO : L ∩ R ∈ D.plan)
variable (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)

include hs hold hL hR hLA hRA hO hcover in
/-- Initialization on the exact recursive seed, including every actual
controller cap and retained higher proper occurrence. -/
theorem seed_ready (hA : 3 ≤ A.card) (hLc : 3 ≤ L.card) (hRc : 3 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ 3 →
      ∃ d , D.cell d = (C, i)) : Ready sem hp 0 hA := by
  have hb := CanonicalSeedLifting.predecessor_bountiful sem hA hp hold
    hL hR hLA hRA (Nat.le_of_succ_le hLc) (Nat.le_of_succ_le hRc) hO hcover
    (fun C hC hCA i hi hic hi2 => hcomplete C hC hCA i hi hic (by omega))
  exact ⟨hs, CanonicalSeedBountiful.bountiful sem hA hp hb hold
    hL hR hLA hRA hLc hRc hO hcover
    (fun C hC hCA hc => hcomplete C hC hCA 3 (by decide) hc le_rfl)⟩

include hs hold hL hR hLA hRA hO hcover in
/-- Finite grade iteration with no supplied seed-readiness premise. The rows
are those of the one recursive constructor, not independently chosen tables. -/
theorem ready n (hA : n + 3 ≤ A.card)
    (hLc : n + 3 ≤ L.card) (hRc : n + 3 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ n + 3 →
      ∃ d , D.cell d = (C, i)) : Ready sem hp n hA := by
  have hseed := seed_ready sem hp hs hold hL hR hLA hRA hO hcover
    (by omega) (by omega) (by omega)
    (fun C hC hCA i hi hic hi3 => hcomplete C hC hCA i hi hic (by omega))
  exact CanonicalRecursiveRecurrence.iterate sem hp hold hL hR hLA hRA hO hcover
    n hA hseed hLc hRc hcomplete

include hs hold hL hR hLA hRA hO hcover in
/-- Actual lower-domain lifting at every constructed grade, including equal
indices, arbitrary lawful prescriptions, literal top, and all auxiliary caps.
No serving controller, alignment, completion, or initial bountifulness is supplied. -/
theorem lift n (hA : n + 3 ≤ A.card)
    (hLc : n + 3 ≤ L.card) (hRc : n + 3 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ n + 3 →
      ∃ d , D.cell d = (C, i))
    {I J} (hI : I ∈ Plan.gradedPlan D.plan)
    (hJ : J ∈ Plan.gradedPlan D.plan) (h : GradedLe I J) (hJk : J.2 ≤ n + 3) :
    CappedLift (CanonicalRecursiveSemantics.rows sem hp n hA) h := by
  apply (GradeCutLifting.lift_iff (CanonicalRecursiveSemantics.rows sem hp n hA)
    (n + 3) h hJk).mp
  apply lift_of_bountiful (ready sem hp hs hold hL hR hLA hRA hO hcover
    n hA hLc hRc hcomplete).2
  · change I ∈ Plan.gradedPlan (CanonicalRecursiveContract.carrier sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]; exact hI
  · change J ∈ Plan.gradedPlan (CanonicalRecursiveContract.carrier sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]; exact hJ


