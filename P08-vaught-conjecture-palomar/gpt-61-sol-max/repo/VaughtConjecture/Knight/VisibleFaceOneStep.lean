/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.AmalgamationPlan.Plan

/-! # Visible faces have one-coordinate visible superfaces

Every proper visible face in an amalgamation plan lies below a visible face obtained by
adding exactly one coordinate — the plan kernel that iterates the paper's literal one-point
Proposition 7.3.3 (`Knight/OnePointRootedExtension.lean`).  Reviewer probe (2026-09-04),
graduated. -/

namespace VaughtConjecture.AmalgamationPlan.Plan

variable {alpha : Type*} [DecidableEq alpha]

theorem IsPlan.exists_visible_card_succ_superface
    {A} {P}
    (hP : IsPlan A P) {B} (hB : B ∈ P) (hne : B ≠ A) :
    ∃ C : Finset alpha, C ∈ P ∧ B ⊂ C ∧ C.card = B.card + 1 := by
  induction hP generalizing B with
  | empty =>
      simp_all
  | singleton a =>
      simp_all
  | @step A a b Q R P ha hb hab hQ hR h_inter h_restr hP ihQ ihR =>
      subst hP
      simp only [Finset.mem_union, Finset.mem_singleton] at hB
      rcases hB with (hBQ | hBR) | hBA
      · by_cases htop : B = A.erase a
        · subst B
          refine ⟨A, by simp, ?_, ?_⟩
          · grind
          · grind
        · grind
      · by_cases htop : B = A.erase b
        · subst B
          refine ⟨A, by simp, ?_, ?_⟩
          · grind
          · grind
        · grind
      · exact absurd hBA hne

