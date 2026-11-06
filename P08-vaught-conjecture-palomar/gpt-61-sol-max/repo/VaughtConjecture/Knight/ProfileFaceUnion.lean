/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.FiniteProfileControllers
import VaughtConjecture.Knight.SlotControllerFamily
import VaughtConjecture.Knight.SeparatedGradeOneCoding
import VaughtConjecture.Knight.MixedGradeInterpolation
import VaughtConjecture.Knight.FreeDiagonal
import VaughtConjecture.Knight.SourceBlockPadding
import Mathlib.Data.Finset.Sort
import VaughtConjecture.Knight.VisibleOrderInterpolation
import VaughtConjecture.Knight.SourceBlockLocalityTransport
import Mathlib.Data.Fintype.Lattice
import VaughtConjecture.Knight.SlackCutPasting

/-! # Occurrence-exact unions of two faces

The common face is identified once; every other occurrence is retained.
The construction is independent of labels and source codes. It supplies a
boundary inventory, not the missing full-scope rows of a support plan.
-/

namespace VaughtConjecture.Knight.ProfileFaceUnion

variable {C X Y : Type*} (f : C ↪ X) (g : C ↪ Y)

abbrev Carrier := X ⊕ {y : Y // y ∉ Set.range g}

local notation "Carrier₀" => Carrier (X := X) g

variable {g} in
def left (x : X) : Carrier₀ := .inl x

open Classical in
noncomputable def right (y : Y) : Carrier₀ :=
  if h : y ∈ Set.range g then .inl (f h.choose) else .inr ⟨y, h⟩

theorem right_shared c : right f g (g c) = left (f c) := by
  
  have h : g c ∈ Set.range g := ⟨c, rfl⟩
  rw [right, dite_eq_left h]
  exact congrArg (fun d => Sum.inl (f d)) (g.injective h.choose_spec)

theorem right_private (y : {y : Y // y ∉ Set.range g}) :
    right f g y = .inr y := by
  classical
  simp only [right, dite_eq_right y.property]

theorem overlap x y :
    left x = right f g y ↔ ∃ c, f c = x ∧ g c = y := by
  
  constructor
  · intro h
    by_cases hy : y ∈ Set.range g
    · obtain ⟨c, rfl⟩ := hy
      rw [right_shared] at h
      exact ⟨c, (Sum.inl.inj h).symm, rfl⟩
    · rw [right, dite_eq_right hy] at h
      cases h
  · grind only [right_shared]

theorem covered (z : Carrier₀) :
    (∃ x, left x = z) ∨ ∃ y, right f g y = z := by
  cases z with
  | inl x => exact Or.inl ⟨x, rfl⟩
  | inr y => exact Or.inr ⟨y, right_private f g y⟩

def paste {V : Type*} (p : X → V) (q : Y → V) : Carrier₀ → V
  | .inl x => p x
  | .inr y => q y

variable {f g} in
theorem paste_right {V : Type*} {p : X → V} {q : Y → V}
    (h : ∀ c, p (f c) = q (g c)) (y : Y) : paste g p q (right f g y) = q y := by
  
  by_cases hy : y ∈ Set.range g
  · obtain ⟨c, rfl⟩ := hy
    rw [right_shared]
    exact h c
  · simp_all [right] <;> aesop


