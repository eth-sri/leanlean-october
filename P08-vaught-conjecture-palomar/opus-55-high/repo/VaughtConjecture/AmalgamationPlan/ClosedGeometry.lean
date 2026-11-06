/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.AmalgamationPlan.Plan
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Closed-set geometry of finite support plans

The inductive construction interface is unchanged. Visible faces are closed under
intersection, so a finite set of points has a least visible superset inside the domain.
This is a canonical support, not a canonical enumeration of that support.
-/

@[expose] public section

namespace VaughtConjecture.AmalgamationPlan.Plan

variable {α : Type*} [DecidableEq α]

/-- Intersections of visible faces are visible. -/
theorem IsPlan.inter_mem {A} {P}
    (hP : IsPlan A P) {X Y : Finset α} (hX : X ∈ P) (hY : Y ∈ P) : X ∩ Y ∈ P := by
  induction hP generalizing X Y with
  | empty =>
    simp only [Finset.mem_singleton] at hX hY
    simp [hX, hY]
  | singleton a =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY ⊢
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp
  | @step A a b Q R P ha hb hab hQ hR hm he hP ihQ ihR =>
    subst P
    have cross {U V : Finset α} (hU : U ∈ Q) (hV : V ∈ R) : U ∩ V ∈ R := by
      have hcut := ihQ hU hm.1
      have hcutR : U ∩ (A.erase a).erase b ∈ R := by
        have hc : U ∩ (A.erase a).erase b ∈ Q ∩ ((A.erase a).erase b).powerset :=
          Finset.mem_inter.mpr ⟨hcut, Finset.mem_powerset.mpr Finset.inter_subset_right⟩
        rw [he] at hc
        exact (Finset.mem_inter.mp hc).1
      have hc := ihR hcutR hV
      have eqn : (U ∩ (A.erase a).erase b) ∩ V = U ∩ V := by
        ext x
        simp only [Finset.mem_inter]
        constructor
        · exact fun h => ⟨h.1.1, h.2⟩
        · intro h
          exact ⟨⟨h.1, Finset.mem_erase.mpr
            ⟨(Finset.mem_erase.mp (hR.subset_of_mem hV h.2)).1,
              hQ.subset_of_mem hU h.1⟩⟩, h.2⟩
      rwa [eqn] at hc
    simp only [Finset.mem_union, Finset.mem_singleton] at hX hY ⊢
    rcases hX with (hX | hX) | rfl
    · rcases hY with (hY | hY) | rfl
      · exact Or.inl (Or.inl (ihQ hX hY))
      · exact Or.inl (Or.inr (cross hX hY))
      · rw [Finset.inter_eq_left.mpr ((hQ.subset_of_mem hX).trans (Finset.erase_subset _ _))]
        exact Or.inl (Or.inl hX)
    · rcases hY with (hY | hY) | rfl
      · rw [Finset.inter_comm]; exact Or.inl (Or.inr (cross hY hX))
      · exact Or.inl (Or.inr (ihR hX hY))
      · rw [Finset.inter_eq_left.mpr ((hR.subset_of_mem hX).trans (Finset.erase_subset _ _))]
        exact Or.inl (Or.inr hX)
    · rcases hY with (hY | hY) | rfl
      · rw [Finset.inter_eq_right.mpr ((hQ.subset_of_mem hY).trans (Finset.erase_subset _ _))]
        exact Or.inl (Or.inl hY)
      · rw [Finset.inter_eq_right.mpr ((hR.subset_of_mem hY).trans (Finset.erase_subset _ _))]
        exact Or.inl (Or.inr hY)
      · simp

end VaughtConjecture.AmalgamationPlan.Plan
