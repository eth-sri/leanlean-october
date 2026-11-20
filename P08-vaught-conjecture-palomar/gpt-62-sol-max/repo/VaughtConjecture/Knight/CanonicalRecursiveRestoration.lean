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

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveRestoration

open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan

open CanonicalRecursiveSuccessorRows

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

abbrev LowerBountiful (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card)
    (P : CanonicalRecursiveContract.Stage sem n (Nat.le_of_succ_le hA)) :=
  (GradeCutBoundary.rows (predecessor sem n hA) (n + 2) P.rows).IsBountiful

variable {sem : Semantics D} {n : ℕ} {hA : n + 3 ≤ A.card}
  (S : CanonicalRecursiveContract.Step sem n hA)

variable (hb : LowerBountiful sem n hA S.prev) {C : Finset ι}

variable (hC : C ∈ D.plan) (hCc : n + 2 ≤ C.card)

include hb hC hCc in
theorem lower_clause : CappedLift (rows S)
    (show GradedLe (C, n + 2) (A, n + 2) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  apply CanonicalRecursiveLifting.lower_lift S _ le_rfl
  apply (GradeCutLifting.lift_iff S.prev.rows (n + 2) _ le_rfl).mp
  apply lift_of_bountiful hb
  · change (C, n + 2) ∈ Plan.gradedPlan (predecessor sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]
    exact Plan.mem_gradedPlan.mpr ⟨hC, by omega, hCc⟩
  · change (A, n + 2) ∈ Plan.gradedPlan (predecessor sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]
    exact Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem, by omega, Nat.le_of_succ_le hA⟩


end

end VaughtConjecture.Knight.CanonicalRecursiveRestoration
