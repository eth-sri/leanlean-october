
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalSeedLifting
import VaughtConjecture.Knight.SingleFaceTailRestoration
import VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport
import VaughtConjecture.Knight.GradeCutLifting

/-! # Predecessor-powered restoration on the actual recursive seed

The predecessor supplies the lower lift through exact occurrence and row
transport. The lower ambient is constructed, not supplied. Arbitrary distinct
lower labels, including top and upper-invisible values, remain literal.
-/

namespace VaughtConjecture.Knight.CanonicalSeedRestoration
open    CoatomBoundaryExtension AmalgamationPlan
open CanonicalRecursiveSeedRows

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card)
variable (hp : AvoidsValue D.scope A)
abbrev LowerBountiful :=
  (GradeCutBoundary.rows (predecessor sem hA) 2 (predecessorRows sem hA hp)).IsBountiful
variable (hb : LowerBountiful sem hA hp) {C : Finset ι}
variable (hC : C ∈ D.plan) (hCc : 2 ≤ C.card)

local notation "rows₀" => rows sem hA hp

include hb hC hCc in
theorem lower_clause : CappedLift (rows₀)
    (show GradedLe (C, 2) (A, 2) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  apply CanonicalSeedLifting.lower_lift sem hA hp _ le_rfl
  apply (GradeCutLifting.lift_iff (predecessorRows sem hA hp) 2 _ le_rfl).mp
  apply lift_of_bountiful hb
  · simp_all [Plan.gradedPlan] <;> aesop
  · 
    exact Plan.mem_gradedPlan.mpr
      ⟨D.isPlan.domain_mem, (by decide : 0 < 2), Nat.le_of_succ_le hA⟩

local notation "GradedLe₀" => GradedLe (C, 3) (A, 3)

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows sem hA hp) (A, 3)

include hb hC hCc in
/-- Restore a constructed owner-capped lift. The capped lift is an internal
input to this composition lemma, not an assumed public active-branch result. -/
theorem restore
    {p : (carrier sem hA).below (C, 3) → ExtOrd}
    (hpr : RespectsSemanticsBelow (rows₀) (C, 3) p)
    {u q : (carrier sem hA).below (A, 3) → ExtOrd}
    (hu : RespectsSemanticsBelow₀ u)
    {M γ : ExtOrd} (hM : SelfVis 3 M) (hγM : γ ≤ M)
    (hread : ∀ e, u (CellScheme.below.mono
      (show GradedLe₀ from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) =
        min (p e) M)
    (hhigh : ∀ e ,
      (carrier sem hA).grade e.1 = 3 → p e ≤ M)
    (hcap : CappedEq u q γ) :
    ∃ r ,
      RespectsSemanticsBelow₀ r ∧
      (∀ e, r (CellScheme.below.mono
        (show GradedLe₀ from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) =
          p e) ∧
      (CappedEq r q γ) ∧
      ∀ d, 2 < (carrier sem hA).grade d.1 → r d ≤ M := by
  obtain ⟨r, hr, hrlit, hrM, hrbound⟩ := SingleFaceTailRestoration.exists_restore
    (rows₀) (D.isPlan.subset_of_mem hC)
    (lower_clause sem hA hp hb hC hCc) hpr hu hM hread hhigh
  exact ⟨r, hr, hrlit, fun d =>
    (GradeTailRestoration.cap_below (hrM d) hγM).trans (hcap d), hrbound⟩

include hb hC hCc in
/-- Complete inactive branch, uniformly in the successor grade. No serving
controller, completion, or lawful lower ambient is an input. -/
theorem inactive
    {p}
    (hpr : RespectsSemanticsBelow (rows₀) (C, 3) p)
    {q}
    (hqr : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis 3 γ)
    (hag : ∀ e, min (q (CellScheme.below.mono
      (show GradedLe₀ from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e)) γ =
        min (p e) γ)
    (hhigh : ∀ e ,
      (carrier sem hA).grade e.1 = 3 → p e ≤ γ) :
    ∃ r ,
      RespectsSemanticsBelow₀ r ∧
      (CappedEq r q γ) ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe₀ from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) =
          p e :=
  SingleFaceTailRestoration.exists_inactive (rows₀) (D.isPlan.subset_of_mem hC)
    (lower_clause sem hA hp hb hC hCc) hpr hqr hγ hag hhigh


