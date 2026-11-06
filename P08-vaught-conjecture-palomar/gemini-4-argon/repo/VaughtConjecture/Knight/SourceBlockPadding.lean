/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PositiveNormalization

/-! # Reserving an initial source block

Left addition by omega shifts finite coded sources by one block. Both the shift
and its partial inverse commute with replacement at every threshold, including
thresholds above the owner's grade. Thus source precomposition uses an actual
witness, not an unrestricted composition principle. Only a construction-owned
row is changed; the semantic rows it respects remain fixed.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

namespace SourceBlockPadding

def pad : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some α) => ofOrd (Ordinal.omega0 + α)

@[simp] theorem pad_ofOrd (α : Ordinal.{0}) : pad (ofOrd α) = ofOrd (Ordinal.omega0 + α) := rfl

theorem pad_mono : Monotone pad := by
  intro x y hxy
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · exact bot_le
  · rw [top_le_iff.mp hxy]
  · rcases ExtOrd.cases y with rfl | rfl | ⟨β, rfl⟩
    · exact False.elim (not_ofOrd_le_bot _ hxy)
    · exact le_top
    · exact ofOrd_le_ofOrd.mpr (add_le_add_right (ofOrd_le_ofOrd.mp hxy) _)

theorem pad_reflects_bottom (x : ExtOrd) (hx : pad x = ⊥) : x = ⊥ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rfl
  · exact False.elim (top_ne_bot hx)
  · exact False.elim (ofOrd_ne_bot _ hx)

theorem pad_decomposition (α : Ordinal.{0}) :
    Ordinal.omega0 + α =
      Ordinal.omega0 * (1 + α / Ordinal.omega0) + (finitePart α : ℕ) := by
  rw [mul_add, mul_one, add_assoc]
  exact congrArg (fun z => Ordinal.omega0 + z) (decomposition α).symm

theorem finitePart_pad (α : Ordinal.{0}) : finitePart (Ordinal.omega0 + α) = finitePart α := by
  rw [pad_decomposition, finitePart_code]

theorem limitPart_pad (α : Ordinal.{0}) :
    limitPart (Ordinal.omega0 + α) = Ordinal.omega0 + limitPart α := by
  rw [pad_decomposition, limitPart_code, mul_add, mul_one]
  rfl

/-- Padding commutes with every replacement, with no threshold bound. -/
theorem pad_comm (x : ExtOrd) (k i : ℕ) :
    pad (extVisibilityReplace x k i) = extVisibilityReplace (pad x) k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rfl
  · rfl
  · rw [pad_ofOrd, extVisibilityReplace_ofOrd, extVisibilityReplace_ofOrd,
      visibilityReplace, visibilityReplace, finitePart_pad]
    split_ifs
    · rw [ordinalReplace, ordinalReplace, pad_ofOrd, limitPart_pad, add_assoc]
    · rfl

theorem pad_step (K : ℕ) : IsStepShifter K pad where
  map_bot := rfl
  mono := pad_mono
  selfVis x k _ hx := by rw [← pad_comm, hx]
  blockwise ξ := by
    refine Or.inl ⟨Ordinal.omega0 + limitPart ξ, ?_, fun i _ => ?_⟩
    · rw [finitePart_pad, finitePart_limitPart]
    · rw [pad_ofOrd, add_assoc]
  bot_blocks ξ ζ _ hx := False.elim (ofOrd_ne_bot _ hx)

open Classical in
def unpad : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some α) => if Ordinal.omega0 ≤ α then ofOrd (α - Ordinal.omega0) else ⊥

@[simp] theorem unpad_bot : unpad ⊥ = ⊥ := rfl

open Classical in
theorem unpad_ofOrd (α : Ordinal.{0}) :
    unpad (ofOrd α) = if Ordinal.omega0 ≤ α then ofOrd (α - Ordinal.omega0) else ⊥ := rfl

theorem unpad_pad (x : ExtOrd) : unpad (pad x) = x := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rfl
  · rfl
  · rw [pad_ofOrd, unpad_ofOrd, ite_eq_left le_self_add, Ordinal.add_sub_cancel]

theorem unpad_mono : Monotone unpad := by
  classical
  intro x y hxy
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · exact bot_le
  · rw [top_le_iff.mp hxy]
  · rcases ExtOrd.cases y with rfl | rfl | ⟨β, rfl⟩
    · exact False.elim (not_ofOrd_le_bot _ hxy)
    · exact le_top
    · rw [unpad_ofOrd, unpad_ofOrd]
      by_cases hα : Ordinal.omega0 ≤ α
      · have hβ := hα.trans (ofOrd_le_ofOrd.mp hxy)
        rw [ite_eq_left hα, ite_eq_left hβ]
        exact ofOrd_le_ofOrd.mpr (Ordinal.sub_le.mpr
          ((ofOrd_le_ofOrd.mp hxy).trans_eq (Ordinal.add_sub_cancel_of_le hβ).symm))
      · rw [ite_eq_right hα]; exact bot_le

/-- The erased first block is a whole block, so the inverse also commutes at
thresholds above the eventual owner grade. -/
theorem unpad_comm (x : ExtOrd) (k i : ℕ) :
    unpad (extVisibilityReplace x k i) = extVisibilityReplace (unpad x) k i := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rfl
  · rfl
  · by_cases hα : Ordinal.omega0 ≤ α
    · have hrep : ofOrd α = pad (ofOrd (α - Ordinal.omega0)) := by
        rw [pad_ofOrd, Ordinal.add_sub_cancel_of_le hα]
      rw [hrep, ← pad_comm, unpad_pad, unpad_pad]
    · have hlt := not_le.mp hα
      obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hlt
      have hf := finitePart_natCast n
      have hl := limitPart_natCast n
      rw [unpad_ofOrd, ite_eq_right hα, extVisibilityReplace_bot,
        extVisibilityReplace_ofOrd, visibilityReplace]
      split_ifs
      · rw [ordinalReplace, hl, zero_add, unpad_ofOrd,
          ite_eq_right (not_le.mpr (Ordinal.natCast_lt_omega0 i))]
      · rw [unpad_ofOrd, ite_eq_right hα]

/-- A direct source change for an arbitrary faithful witness; no composition
closure assumption and no restriction on the suppressor are needed. -/
theorem witness_precompose_unpad {g : ℕ → ExtOrd} {τ : ExtOrd → ExtOrd}
    (hτ : Witness g τ) : Witness g (fun x => τ (unpad x)) where
  anti := hτ.anti
  vis := hτ.vis
  bot := hτ.bot
  mono := hτ.mono.comp unpad_mono
  clause5 x k hx i hi := by rw [unpad_comm]; exact hτ.clause5 _ k hx i hi

/-- Finite coded blocks move by exactly one; offsets and owner-grade coding stay fixed. -/
theorem pad_code (b j : ℕ) : pad (ofOrd (Ordinal.omega0 * b + j)) =
    ofOrd (Ordinal.omega0 * (b + 1 : ℕ) + j) := by
  rw [pad_ofOrd, ← add_assoc]
  congr 2
  rw [show b + 1 = 1 + b by omega, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
