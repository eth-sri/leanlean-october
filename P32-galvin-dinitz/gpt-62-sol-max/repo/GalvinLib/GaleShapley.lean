/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GalvinLib.Kernel

/-! # Stable matchings as kernels of the preference relation -/

@[expose] public section

namespace Galvin

open Finset

variable {E M W R : Type*} (l : E → M) (r : E → W)

/-- Distinct pairs that have a common partner. -/
def Incident (x y : E) : Prop :=
  x ≠ y ∧ (l x = l y ∨ r x = r y)

/-- There is an arc to any pair preferred by the partner at the common endpoint. -/
def Pref [LT R] (p q : E → R) (x y : E) : Prop :=
  (l x = l y ∧ p y < p x) ∨ (r x = r y ∧ q y < q x)

/-- A finite set of acceptable pairs has a stable matching if preferences are strict. -/
theorem stable [LinearOrder R] (p q : E → R)
    (hp : ∀ ⦃x y⦄, l x = l y → p x = p y → x = y)
    (hq : ∀ ⦃x y⦄, r x = r y → q x = q y → x = y) :
    HasKernels (Incident l r) (Pref l r p q) := by
  classical
  refine strongInduction fun S ih => ?_
  let top (x : E) := x ∈ S ∧ ∀ y ∈ S, l x = l y → p x ≤ p y
  -- When favourites collide, discard the one the common partner likes less.
  by_cases h : ∃ a b, top a ∧ top b ∧ r a = r b ∧ q a < q b
  · obtain ⟨a, b, ha, hb, hab, hlt⟩ := h
    obtain ⟨K, hK, hind, habs⟩ := ih _ (erase_ssubset hb.1)
    have := habs a (by grind)
    refine ⟨K, hK.trans (erase_subset _ _), hind, ?_⟩
    grind [Pref, lt_trans]
  · refine ⟨_, filter_subset top S, ?_, ?_⟩
    · grind [Incident, le_antisymm, lt_trichotomy]
    · intro x hx
      obtain ⟨y, hy, hmin⟩ := exists_min_image (S.filter (fun y => l y = l x)) p
        ⟨x, by simp [hx]⟩
      refine ⟨y, ?_, ?_⟩ <;> grind [Pref, lt_of_le_of_ne]

end Galvin
