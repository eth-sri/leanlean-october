/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.AmalgamationPlan.Plan

@[expose] public section

namespace VaughtConjecture.AmalgamationPlan.Plan

variable {alpha : Type*} [DecidableEq alpha]

theorem IsPlan.exists_visible_card_succ_superface
    {A : Finset alpha} {P : Finset (Finset alpha)}
    (hP : IsPlan A P) {B : Finset alpha} (hB : B ∈ P) (hne : B ≠ A) :
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
          grind
        grind
      · by_cases htop : B = A.erase b
        · subst B
          refine ⟨A, by simp, ?_, ?_⟩
          · grind
          grind
        grind
      · exact absurd hBA hne

end VaughtConjecture.AmalgamationPlan.Plan
