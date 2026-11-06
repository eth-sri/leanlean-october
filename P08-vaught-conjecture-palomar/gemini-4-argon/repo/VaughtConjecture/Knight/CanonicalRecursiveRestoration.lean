/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveLifting
public import VaughtConjecture.Knight.SingleFaceTailRestoration
public import VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport
public import VaughtConjecture.Knight.GradeCutLifting

/-! # Predecessor-powered restoration on the actual recursive successor

The predecessor supplies the lower lift through exact occurrence and row
transport. The lower ambient is constructed, not supplied. Arbitrary distinct
lower labels, including top and upper-invisible values, remain literal.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalRecursiveRestoration
open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan CanonicalRecursiveSuccessorRows

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)
  (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))
abbrev LowerBountiful :=
  (GradeCutBoundary.rows (predecessor sem n hA) (n + 3) P.rows).IsBountiful
variable (hb : LowerBountiful sem n hA P) {C : Finset ι}
  (hC : C ∈ D.plan) (hCc : n + 3 ≤ C.card)

include hb hC hCc in
theorem lower_clause : CappedLift (rows sem n hA hp P)
    (show GradedLe (C, n + 3) (A, n + 3) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  apply CanonicalRecursiveLifting.lower_lift sem n hA hp P _ le_rfl
  apply (GradeCutLifting.lift_iff P.rows (n + 3) _ le_rfl).mp
  apply lift_of_bountiful hb
  · change (C, n + 3) ∈ Plan.gradedPlan (predecessor sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]
    exact Plan.mem_gradedPlan.mpr ⟨hC, by omega, hCc⟩
  · change (A, n + 3) ∈ Plan.gradedPlan (predecessor sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]
    exact Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem, by omega, Nat.le_of_succ_le hA⟩
