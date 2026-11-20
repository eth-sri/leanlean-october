/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutBoundary

/-! # Exact lifting transport across an actual grade cut -/

@[expose] public section

namespace VaughtConjecture.Knight.GradeCutLifting
open Transform Value ExtOrd CoatomBoundaryExtension GradeCutBoundary
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (k : ℕ)

theorem lift_iff {I J} (h : GradedLe I J) (hJ : J.2 ≤ k) :
    CappedLift (rows D k sem) h ↔ CappedLift sem h :=
  CappedLift.equiv_iff (belowEquiv D k I (h.2.trans hJ)) (belowEquiv D k J hJ)
    (fun _ => rfl) rfl (respects_iff D k sem I _) (respects_iff D k sem J hJ)

end VaughtConjecture.Knight.GradeCutLifting
