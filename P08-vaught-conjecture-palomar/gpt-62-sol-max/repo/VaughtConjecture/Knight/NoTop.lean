/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

open Cardinal Ordinal

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe u

/-- The block levels below `ω₁` stay below `ω₁` (`card (ω + ω·ξ) = ℵ₀ + ℵ₀·card ξ < ℵ₁`). -/
theorem blockLevel_lt_ord_aleph_one {ξ : Ordinal.{0}} (hξ : ξ < (aleph 1).ord) :
    blockLevel ξ < (aleph 1).ord := by
  rw [lt_ord] at hξ ⊢
  unfold blockLevel
  rw [card_add, card_mul, card_omega0]
  exact add_lt_of_lt (aleph0_le_aleph 1) aleph0_lt_aleph_one
    (mul_lt_of_lt (aleph0_le_aleph 1) aleph0_lt_aleph_one hξ)

end VaughtConjecture.Knight
