
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.CoatomBoundaryExtension
import VaughtConjecture.Knight.FullScopeBountiful
import VaughtConjecture.Knight.PartialSections

/-! # Exhaustive lifting reduction at the actual grade ceiling

Clamping a nominal grade loses no occurrence when all actual grades are
bounded. The original cap is retained, using visibility only downwards.
Same-scope grade changes then reduce the ledger to same-grade pairs.
-/

namespace VaughtConjecture.Knight.EffectiveGradeLifting
open    CoatomBoundaryExtension AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable {sem : Semantics D} {K : ℕ} (hK : BoundedBy D.grade K)

def cut (J : GradedIndex ι) := (J.1, min J.2 K)

local notation "cut₀" => cut (K := K)

def equiv J : D.below (cut₀ J) ≃ D.below J where
  toFun d := ⟨d.1, d.2.1, (le_min_iff.mp d.2.2).1⟩
  invFun d := ⟨d.1, d.2.1, le_min d.2.2 (hK d.1)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem respects_iff J (p : BelowLabels D (cut₀ J)) :
    RespectsSemanticsBelow sem (cut₀ J) p ↔
      RespectsSemanticsBelow sem J (p ∘ (equiv hK J).symm) :=
  respects_iff_of_equiv (equiv hK J) (fun _ => rfl) (fun _ _ => Iff.rfl)
    (fun _ _ _ => rfl) p

theorem pullback_respects {J} {q}
    (hq : RespectsSemanticsBelow sem J q) :
    RespectsSemanticsBelow sem (cut₀ J) (q ∘ equiv hK J) := by
  apply (respects_iff hK J _).mpr
  exact hq

omit [DecidableEq ι] in
theorem cut_le {I J : GradedIndex ι} (h : GradedLe I J) :
    GradedLe (cut₀ I) (cut₀ J) :=
  ⟨h.1, min_le_min_right K h.2⟩

include hK in
/-- Transfer the actual capped lift, not just section existence. -/
theorem lift {I J} (h : GradedLe I J)
    (hl : CappedLift sem (cut_le (K := K) h)) : CappedLift sem h := by
  apply CappedLift.of_equiv (equiv hK I) (equiv hK J) (fun _ => rfl)
    (min_le_left _ _) (fun _ hp => pullback_respects hK hp) _ hl
  intro q
  exact ⟨fun hq => pullback_respects hK hq, fun hq => by
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using (respects_iff hK J _).mp hq⟩

/-- Every literal graded pair follows from same-grade pairs, without
completeness or a hypothesis about an already extended ambient. -/
theorem bountiful_of_same_grade
    (hsame : ∀ C B i, (C, i) ∈ Plan.gradedPlan D.plan →
      (B, i) ∈ Plan.gradedPlan D.plan → (h : C ⊆ B) →
      CappedLift sem (show GradedLe (C, i) (B, i) from ⟨h, le_rfl⟩)) :
    sem.IsBountiful := by
  rintro ⟨C, i⟩ ⟨B, j⟩ hCI hBJ h _
  have hBi : (B, i) ∈ Plan.gradedPlan D.plan := Plan.mem_gradedPlan.mpr
    ⟨(Plan.mem_gradedPlan.mp hBJ).1, (Plan.mem_gradedPlan.mp hCI).2.1,
      h.2.trans (Plan.mem_gradedPlan.mp hBJ).2.2⟩
  let hi : GradedLe (C, i) (B, i) := ⟨h.1, le_rfl⟩
  let hj : GradedLe (B, i) (B, j) := ⟨Finset.Subset.refl _, h.2⟩
  exact CappedLift.comp   (hsame C B i hCI hBi h.1)
    (bountiful_same_scope sem hj)

include hK in
/-- Only the nonempty effective grades need separate lifting proofs. -/
theorem bountiful_of_bounded_same_grade (hpos : 0 < K)
    (hsame : ∀ C B i, (C, i) ∈ Plan.gradedPlan D.plan →
      (B, i) ∈ Plan.gradedPlan D.plan → i ≤ K → (h : C ⊆ B) →
      CappedLift sem (show GradedLe (C, i) (B, i) from ⟨h, le_rfl⟩)) :
    sem.IsBountiful := by
  apply bountiful_of_same_grade
  intro C B i hC hB h
  apply lift hK
  have mem (S : Finset ι) (hm : (S, i) ∈ Plan.gradedPlan D.plan) :
      (S, min i K) ∈ Plan.gradedPlan D.plan := by
    obtain ⟨hs, hi, hc⟩ := Plan.mem_gradedPlan.mp hm
    exact Plan.mem_gradedPlan.mpr ⟨hs, lt_min hi hpos, (min_le_left _ _).trans hc⟩
  exact hsame C B (min i K) (mem C hC) (mem B hB) (min_le_right _ _) h

