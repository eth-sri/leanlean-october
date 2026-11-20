/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.AmalgamationPlan.Plan
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace VaughtConjecture.AmalgamationPlan.Plan

variable {α : Type*} [DecidableEq α]

/-- Intersections of visible faces are visible. -/
theorem IsPlan.inter_mem {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) {X Y : Finset α} (hX : X ∈ P) (hY : Y ∈ P) : X ∩ Y ∈ P := by
  induction hP generalizing X Y with
  | empty =>
    simp_all
  | singleton a =>
    grind
  | @step A a b Q R P ha hb hab hQ hR hm he hP ihQ ihR =>
    subst P
    have cross {U V : Finset α} (hU : U ∈ Q) (hV : V ∈ R) : U ∩ V ∈ R := by
      have hcut := ihQ hU hm.1
      have hcutR : U ∩ (A.erase a).erase b ∈ R := by
        have hc : U ∩ (A.erase a).erase b ∈ Q ∩ ((A.erase a).erase b).powerset :=
          Finset.mem_inter.mpr ⟨hcut, Finset.mem_powerset.mpr Finset.inter_subset_right⟩
        simp_all
      have hc := ihR hcutR hV
      have eqn : (U ∩ (A.erase a).erase b) ∩ V = U ∩ V := by
        ext x
        simp only [Finset.mem_inter]
        constructor
        · tauto
        · intro h
          exact ⟨⟨h.1, Finset.mem_erase.mpr
            ⟨(Finset.mem_erase.mp (hR.subset_of_mem hV h.2)).1,
              hQ.subset_of_mem hU h.1⟩⟩, h.2⟩
      rwa [eqn] at hc
    simp only [Finset.mem_union, Finset.mem_singleton] at hX hY ⊢
    rcases hX with (hX | hX) | rfl
    · rcases hY with (hY | hY) | rfl
      · solve_by_elim
      · simp_all
      · rw [Finset.inter_eq_left.mpr ((hQ.subset_of_mem hX).trans (Finset.erase_subset _ _))]
        simp_all
    · rcases hY with (hY | hY) | rfl
      · rw [Finset.inter_comm]; simp_all
      · simp_all
      · rw [Finset.inter_eq_left.mpr ((hR.subset_of_mem hX).trans (Finset.erase_subset _ _))]
        simp_all
    · rcases hY with (hY | hY) | rfl
      · rw [Finset.inter_eq_right.mpr ((hQ.subset_of_mem hY).trans (Finset.erase_subset _ _))]
        simp_all
      · rw [Finset.inter_eq_right.mpr ((hR.subset_of_mem hY).trans (Finset.erase_subset _ _))]
        simp_all
      · simp

end VaughtConjecture.AmalgamationPlan.Plan
