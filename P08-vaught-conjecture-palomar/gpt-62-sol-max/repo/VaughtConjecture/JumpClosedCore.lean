/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite

@[expose] public section

namespace VaughtConjecture.JumpClosed

open Filter

variable {I : Type*}

/-- The jump at `K` of a band vector: coordinates at most `K` stay, the others escape to `⊤`. -/
def jump (K : ℕ) (u : I → ℕ∞) : I → ℕ∞ := fun i => if u i ≤ K then u i else ⊤

/-- A vector is `K`-approximated by `u` when `u` agrees with it at its finite coordinates and
strictly exceeds `K` at its infinite ones. -/
def Approximates (K : ℕ) (u r : I → ℕ∞) : Prop :=
  ∀ i, (r i ≠ ⊤ → u i = r i) ∧ (r i = ⊤ → (K : ℕ∞) < u i)

/-- The jump at `K` of a `K`-approximation is the vector itself, once `K` bounds its finite
coordinates. -/
theorem jump_eq_of_approximates {K : ℕ} {u r : I → ℕ∞} (h : Approximates K u r)
    (hK : ∀ i, r i ≠ ⊤ → r i ≤ K) : jump K u = r := by grind +locals

end VaughtConjecture.JumpClosed
