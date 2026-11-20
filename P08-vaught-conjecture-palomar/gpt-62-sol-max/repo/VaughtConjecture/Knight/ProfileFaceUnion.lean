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
public import VaughtConjecture.Knight.CoupledGradeOne





@[expose] public section

namespace VaughtConjecture.Knight.ProfileFaceUnion

variable {C X Y : Type*} (f : C ↪ X) (g : C ↪ Y)

abbrev Carrier := X ⊕ {y : Y // y ∉ Set.range g}

def left (x : X) : Carrier (X := X) g := .inl x

open Classical in
noncomputable def right (y : Y) : Carrier (X := X) g :=
  if h : y ∈ Set.range g then .inl (f h.choose) else .inr ⟨y, h⟩

theorem right_shared (c : C) : right f g (g c) = left g (f c) := by grind +locals

theorem right_private (y : {y : Y // y ∉ Set.range g}) :
    right f g y = .inr y := by grind +locals

theorem overlap (x : X) (y : Y) :
    left g x = right f g y ↔ ∃ c, f c = x ∧ g c = y := by grind +locals

theorem covered (z : Carrier (X := X) g) :
    (∃ x, left g x = z) ∨ ∃ y, right f g y = z := by
  cases z with
  | inl x => tauto
  | inr y => exact Or.inr ⟨y, right_private f g y⟩

def paste {V : Type*} (p : X → V) (q : Y → V) : Carrier (X := X) g → V
  | .inl x => p x
  | .inr y => q y

theorem paste_pred {V : Type*} {R : V → Prop} {p : X → V} {q : Y → V}
    (hp : ∀ x, R (p x)) (hq : ∀ y, R (q y)) (z : Carrier (X := X) g) : R (paste g p q z) := by aesop

theorem paste_rel {V W : Type*} {R : V → W → Prop} {p : X → V} {q : Y → V}
    {p' : X → W} {q' : Y → W} (hp : ∀ x, R (p x) (p' x)) (hq : ∀ y, R (q y) (q' y))
    (z : Carrier (X := X) g) : R (paste g p q z) (paste g p' q' z) := by aesop

theorem paste_right {V : Type*} {p : X → V} {q : Y → V}
    (h : ∀ c, p (f c) = q (g c)) (y : Y) : paste g p q (right f g y) = q y := by grind +locals

noncomputable instance [Fintype X] [Fintype Y] : Fintype (Carrier (X := X) g) := by
  classical
  unfold Carrier
  infer_instance

end VaughtConjecture.Knight.ProfileFaceUnion
