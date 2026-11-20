/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutBoundary
public import VaughtConjecture.Knight.CoatomBoundaryExtension

@[expose] public section

namespace VaughtConjecture.Knight.GradeCutLifting

open Transform Value ExtOrd CoatomBoundaryExtension GradeCutBoundary

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (k : ℕ)

theorem lift_iff {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ k) :
    CappedLift (rows D k sem) h ↔ CappedLift sem h := by
  let eI := belowEquiv D k I (h.2.trans hJ)
  let eJ := belowEquiv D k J hJ
  exact ⟨CappedLift.of_equiv eI eJ (fun _ => rfl) le_rfl
      (respects_iff D k sem I (h.2.trans hJ)) (respects_iff D k sem J hJ),
    CappedLift.of_pullback eI eJ (fun _ => rfl) le_rfl
      (respects_iff D k sem I (h.2.trans hJ)) (respects_iff D k sem J hJ)⟩

/-- Transport both old-face lifts to the scheme restricted to the cutoff. -/
def cutCover {I : Finset ι × ℕ} (W : CutCover sem I k) : CutCover (rows D k sem) I k where
  L := W.L
  R := W.R
  covered d _ := W.covered (toCell D k d) (grade_bound D k d)
  le := W.le
  left_lift := (lift_iff sem k W.le le_rfl).mpr W.left_lift
  right_lift := (lift_iff sem k target_le_right le_rfl).mpr W.right_lift

end VaughtConjecture.Knight.GradeCutLifting
