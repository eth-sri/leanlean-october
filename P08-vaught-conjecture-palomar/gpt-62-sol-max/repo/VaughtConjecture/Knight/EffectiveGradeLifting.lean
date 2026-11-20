/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomBoundaryExtension
public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.SectionExtension

@[expose] public section

namespace VaughtConjecture.Knight.EffectiveGradeLifting

open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable {sem : Semantics D} {K : ℕ} (hK : ∀ d : Cell D, D.grade d ≤ K)

def cut (J : Finset ι × ℕ) : Finset ι × ℕ := (J.1, min J.2 K)

omit [DecidableEq ι] in
theorem cut_le {I J : Finset ι × ℕ} (h : GradedLe I J) :
    GradedLe (cut (K := K) I) (cut (K := K) J) :=
  ⟨h.1, min_le_min_right K h.2⟩

include hK in
/-- Transfer the actual capped lift, not just section existence. -/
theorem lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hl : CappedLift sem (cut_le (K := K) h)) : CappedLift sem h := 
  CappedLift.of_equiv (CellScheme.cutoffEquiv I (fun d => hK d.1))
    (CellScheme.cutoffEquiv J (fun d => hK d.1)) (fun _ => rfl) (min_le_left _ _)
    (CellScheme.cutoff_respects I (fun d => hK d.1)) (CellScheme.cutoff_respects J (fun d => hK d.1)) hl

/-- Every literal graded pair follows from same-grade pairs, without
completeness or a hypothesis about an already extended ambient. -/
theorem bountiful_of_same_grade
    (hsame : ∀ (C B : Finset ι) (i : ℕ), (C, i) ∈ Plan.gradedPlan D.plan →
      (B, i) ∈ Plan.gradedPlan D.plan → (h : C ⊆ B) →
      CappedLift sem (show GradedLe (C, i) (B, i) from ⟨h, le_rfl⟩)) :
    sem.IsBountiful := by
  rintro ⟨C, i⟩ ⟨B, j⟩ hCI hBJ h _
  have hBi : (B, i) ∈ Plan.gradedPlan D.plan := Plan.mem_gradedPlan.mpr
    ⟨(Plan.mem_gradedPlan.mp hBJ).1, (Plan.mem_gradedPlan.mp hCI).2.1,
      h.2.trans (Plan.mem_gradedPlan.mp hBJ).2.2⟩
  let hi : GradedLe (C, i) (B, i) := ⟨h.1, le_rfl⟩
  let hj : GradedLe (B, i) (B, j) := ⟨Finset.Subset.refl _, h.2⟩
  exact CappedLift.comp (hIJ := hi) (hJK := hj) (hsame C B i hCI hBi h.1)
    (bountiful_same_scope sem hj)

include hK in
/-- Only the nonempty effective grades need separate lifting proofs. -/
theorem bountiful_of_bounded_same_grade (hpos : 0 < K)
    (hsame : ∀ (C B : Finset ι) (i : ℕ), (C, i) ∈ Plan.gradedPlan D.plan →
      (B, i) ∈ Plan.gradedPlan D.plan → i ≤ K → (h : C ⊆ B) →
      CappedLift sem (show GradedLe (C, i) (B, i) from ⟨h, le_rfl⟩)) :
    sem.IsBountiful := by
  apply bountiful_of_same_grade
  intro C B i hC hB h
  apply lift hK
  have mem (S : Finset ι) (hm : (S, i) ∈ Plan.gradedPlan D.plan) :
      (S, min i K) ∈ Plan.gradedPlan D.plan := by
    obtain ⟨hs, hi, hc⟩ := Plan.mem_gradedPlan.mp hm
    exact Plan.mem_gradedPlan.mpr ⟨hs, lt_min hi hpos, by lia⟩
  aesop

end VaughtConjecture.Knight.EffectiveGradeLifting
