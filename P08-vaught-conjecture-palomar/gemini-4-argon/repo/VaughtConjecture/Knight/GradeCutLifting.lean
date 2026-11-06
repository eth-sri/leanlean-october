/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutBoundary
public import VaughtConjecture.Knight.CoatomBoundaryExtension

/-! # Exact lifting transport across an actual grade cut -/

@[expose] public section

namespace VaughtConjecture.Knight.GradeCutLifting
open Transform Value ExtOrd CoatomBoundaryExtension GradeCutBoundary
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (k : ℕ)

theorem lift_iff {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ k) :
    CappedLift (rows D k sem) h ↔ CappedLift sem h :=
  CappedLift.iff_of_respects_iff (belowEquiv D k I (h.2.trans hJ)) (belowEquiv D k J hJ)
    (fun _ => rfl) (respects_iff D k sem I (h.2.trans hJ)) (respects_iff D k sem J hJ)

