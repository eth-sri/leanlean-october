/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSeedLifting
public import VaughtConjecture.Knight.SingleFaceTailRestoration
public import VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport
public import VaughtConjecture.Knight.GradeCutLifting

/-! # Predecessor-powered restoration on the actual recursive seed

The predecessor supplies the lower lift through exact occurrence and row
transport. The lower ambient is constructed, not supplied. Arbitrary distinct
lower labels, including top and upper-invisible values, remain literal.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalSeedRestoration
open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan CanonicalRecursiveSeedRows

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hA : 3 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)
abbrev LowerBountiful :=
  (GradeCutBoundary.rows (predecessor sem hA) 2 (predecessorRows sem hA hp)).IsBountiful
variable (hb : LowerBountiful sem hA hp) {C : Finset ι}
  (hC : C ∈ D.plan) (hCc : 2 ≤ C.card)

include hb hC hCc in
theorem lower_clause : CappedLift (rows sem hA hp)
    (show GradedLe (C, 2) (A, 2) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  apply CanonicalSeedLifting.lower_lift sem hA hp _ le_rfl
  apply (GradeCutLifting.lift_iff (predecessorRows sem hA hp) 2 _ le_rfl).mp
  apply lift_of_bountiful hb
  · exact Plan.mem_gradedPlan.mpr ⟨hC, Nat.succ_pos 1, hCc⟩
  · exact Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem, Nat.succ_pos 1, Nat.le_of_succ_le hA⟩
