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

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveRestoration
open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan
open CanonicalRecursiveSuccessorRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 1 ≤ A.card)
variable (hp : D.AvoidsScope A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))
abbrev LowerBountiful :=
  (GradeCutBoundary.rows (predecessor sem n hA) n P.rows).IsBountiful
variable (hb : LowerBountiful sem n hA P) {C : Finset ι}
variable (hC : C ∈ D.plan) (hCc : n ≤ C.card)

include hb hC hCc in
theorem lower_clause : CappedLift (rows sem n hA hp P)
    (show GradedLe (C, n) (A, n) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  apply CanonicalRecursiveLifting.lower_lift sem n hA hp P _ le_rfl
  apply (GradeCutLifting.lift_iff P.rows n _ le_rfl).mp
  by_cases hz : n = 0
  · letI : IsEmpty ((GradeCutBoundary.scheme (predecessor sem n hA) n).below (C,n)) :=
      ⟨fun d => (Nat.not_lt_of_ge (d.2.2.trans_eq hz))
        ((GradeCutBoundary.scheme (predecessor sem n hA) n).grade_pos d.1)⟩
    exact lift_empty _
  apply lift_of_bountiful hb
  · change (C, n) ∈ Plan.gradedPlan (predecessor sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]
    exact Plan.mem_gradedPlan.mpr ⟨hC, by omega, hCc⟩
  · change (A, n) ∈ Plan.gradedPlan (predecessor sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]
    exact Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem, by omega, Nat.le_of_succ_le hA⟩

include hb hC hCc in
/-- Restore a constructed owner-capped lift. The capped lift is an internal
input to this composition lemma, not an assumed public active-branch result. -/
theorem restore
    {p : (carrier sem n hA).below (C, n + 1) → ExtOrd}
    (hpr : RespectsSemanticsBelow (rows sem n hA hp P) (C, n + 1) p)
    {u q : (carrier sem n hA).below (A, n + 1) → ExtOrd}
    (hu : RespectsSemanticsBelow (rows sem n hA hp P) (A, n + 1) u)
    {M γ : ExtOrd} (hM : SelfVis (n + 1) M) (hγM : γ ≤ M)
    (hread : ∀ e, u (CellScheme.below.mono
      (show GradedLe (C, n + 1) (A, n + 1) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) =
        min (p e) M)
    (hhigh : ∀ e : (carrier sem n hA).below (C, n + 1),
      (carrier sem n hA).grade e.1 = n + 1 → p e ≤ M)
    (hcap : CappedEq u q γ) :
    ∃ r : (carrier sem n hA).below (A, n + 1) → ExtOrd,
      RespectsSemanticsBelow (rows sem n hA hp P) (A, n + 1) r ∧
      (∀ e, r (CellScheme.below.mono
        (show GradedLe (C, n + 1) (A, n + 1) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) =
          p e) ∧
      CappedEq r q γ ∧
      ∀ d, n < (carrier sem n hA).grade d.1 → r d ≤ M := by
  obtain ⟨r, hr, hrlit, hrM, hrbound⟩ := SingleFaceTailRestoration.exists_restore
    (rows sem n hA hp P) (D.isPlan.subset_of_mem hC)
    (lower_clause sem n hA hp P hb hC hCc) hpr hu hM hread hhigh
  exact ⟨r, hr, hrlit, fun d =>
    (GradeTailRestoration.cap_below (hrM d) hγM).trans (hcap d), hrbound⟩

include hb hC hCc in
/-- Complete inactive branch, uniformly in the successor grade. No serving
controller, completion, or lawful lower ambient is an input. -/
theorem inactive
    {p : (carrier sem n hA).below (C, n + 1) → ExtOrd}
    (hpr : RespectsSemanticsBelow (rows sem n hA hp P) (C, n + 1) p)
    {q : (carrier sem n hA).below (A, n + 1) → ExtOrd}
    (hqr : RespectsSemanticsBelow (rows sem n hA hp P) (A, n + 1) q)
    {γ : ExtOrd} (hγ : SelfVis (n + 1) γ)
    (hag : ∀ e, min (q (CellScheme.below.mono
      (show GradedLe (C, n + 1) (A, n + 1) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e)) γ =
        min (p e) γ)
    (hhigh : ∀ e : (carrier sem n hA).below (C, n + 1),
      (carrier sem n hA).grade e.1 = n + 1 → p e ≤ γ) :
    ∃ r : (carrier sem n hA).below (A, n + 1) → ExtOrd,
      RespectsSemanticsBelow (rows sem n hA hp P) (A, n + 1) r ∧
      CappedEq r q γ ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe (C, n + 1) (A, n + 1) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) =
          p e :=
  SingleFaceTailRestoration.exists_inactive (rows sem n hA hp P) (D.isPlan.subset_of_mem hC)
    (lower_clause sem n hA hp P hb hC hCc) hpr hqr hγ hag hhigh

end
end VaughtConjecture.Knight.CanonicalRecursiveRestoration
