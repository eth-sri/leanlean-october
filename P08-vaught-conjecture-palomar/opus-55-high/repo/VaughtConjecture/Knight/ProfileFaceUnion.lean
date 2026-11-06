/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteProfileControllers
public import VaughtConjecture.Knight.SlotControllerFamily
public import VaughtConjecture.Knight.FreshSourceSlots
public import VaughtConjecture.Knight.SourceBlockPadding
public import VaughtConjecture.Knight.FreeDiagonal
public import Mathlib.Data.Finset.Sort
public import VaughtConjecture.Knight.VisibleOrderInterpolation
public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import Mathlib.Data.Fintype.Lattice
public import VaughtConjecture.Knight.SlackCutPasting

/-! # Occurrence-exact unions of two faces

The common face is identified once; every other occurrence is retained.
The construction is independent of labels and source codes. It supplies a
boundary inventory, not the missing full-scope rows of a support plan.
-/

@[expose] public section

namespace VaughtConjecture.Knight.ProfileFaceUnion

variable {C X Y : Type*} (f : C ↪ X) (g : C ↪ Y)

abbrev Carrier := X ⊕ {y : Y // y ∉ Set.range g}

def left (x : X) : Carrier (X := X) g := .inl x

open Classical in
noncomputable def right (y : Y) : Carrier (X := X) g :=
  if h : y ∈ Set.range g then .inl (f h.choose) else .inr ⟨y, h⟩

theorem right_shared c : right f g (g c) = left g (f c) := by
  classical
  have h : g c ∈ Set.range g := ⟨c, rfl⟩
  rw [right, dite_eq_left h]
  exact congrArg (fun d => Sum.inl (f d)) (g.injective h.choose_spec)

theorem right_private (y : {y : Y // y ∉ Set.range g}) :
    right f g y = .inr y := by
  classical
  simp only [right, dite_eq_right y.property]

theorem overlap x y :
    left g x = right f g y ↔ ∃ c, f c = x ∧ g c = y := by
  classical
  constructor
  · intro h
    by_cases hy : y ∈ Set.range g
    · obtain ⟨c, rfl⟩ := hy
      rw [right_shared] at h
      exact ⟨c, (Sum.inl.inj h).symm, rfl⟩
    · rw [right, dite_eq_right hy] at h
      cases h
  · rintro ⟨c, rfl, rfl⟩
    exact (right_shared f g c).symm

theorem covered (z : Carrier (X := X) g) :
    (∃ x, left g x = z) ∨ ∃ y, right f g y = z := by
  cases z with
  | inl x => exact Or.inl ⟨x, rfl⟩
  | inr y => exact Or.inr ⟨y, right_private f g y⟩

def paste {V : Type*} (p : X → V) (q : Y → V) : Carrier (X := X) g → V
  | .inl x => p x
  | .inr y => q y

theorem paste_right {V} {p} {q : Y → V}
    (h : ∀ c, p (f c) = q (g c)) y : paste g p q (right f g y) = q y := by
  classical
  by_cases hy : y ∈ Set.range g
  · obtain ⟨c, rfl⟩ := hy
    rw [right_shared]
    exact h c
  · rw [right, dite_eq_right hy]
    rfl

end VaughtConjecture.Knight.ProfileFaceUnion
