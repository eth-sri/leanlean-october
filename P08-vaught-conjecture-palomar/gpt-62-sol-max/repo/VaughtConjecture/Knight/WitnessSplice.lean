/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.Domain
public import VaughtConjecture.Knight.WitnessAlgebra
public import VaughtConjecture.Knight.NormalForm

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-- A label is at most its visibility replacement at its own threshold. -/
theorem le_extVisibilityReplace_self (x : ExtOrd) (k : ℕ) : x ≤ extVisibilityReplace x k k := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · exact le_rfl
  · exact le_rfl
  · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
    unfold visibilityReplace
    split_ifs with h
    · unfold ordinalReplace
      calc α = limitPart α + ↑(finitePart α) := (decomposition α).symm
        _ ≤ limitPart α + (k : Ordinal) := add_le_add_right (by exact_mod_cast h.le) _
    · exact le_rfl

theorem limitPart_visibilityReplace (α : Ordinal.{0}) (k i : ℕ) :
    limitPart (visibilityReplace α k i) = limitPart α := by
  unfold visibilityReplace
  split_ifs
  · exact limitPart_limitPart_add_nat α i
  · rfl

end VaughtConjecture.Knight
