import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CappedDonorRetarget
import VaughtConjecture.Knight.CappedDonorRelease
import VaughtConjecture.Knight.CappedDonorNormalization
import VaughtConjecture.Knight.PairedSlotDecoder

/-! # Current-grade normalization and the terminal-block decoding of the two-threshold family
(audit16 §5; note §7, §11 (1), (6))

**Closure under current-grade maps** (`TAdmissible.map`): every bottom-reflecting normalized
witness through the grades currently present (and grade one) preserves two-threshold
admissibility.  LOW transports because a strict *output* antecedent reflects through a monotone
map to a strict source antecedent (`lt_of_map_lt`), the non-top maximum and the cap field commute
with the map (`nonTopMax_map`, `capField_map`), and the frontier commutes once the map commutes
with replacement through `K` (`eC_map`); HIGH transports through `cut_map`.  No commutation
through the private arity is needed.

**Canonical normalization on the complete inventory** (`TField`, `TState.profile`,
`normalizeT`): the paired point/orbit encoder built from the values of the **complete** source
vector — every receiving field *and the stored cutoff* — applied to every field.  It preserves
admissibility (`normalizeT_tadmissible`) and synchronization, yields coded (`normalizeT_coded`,
block bound `2·|TField|`) and `j`-short (`normalizeT_short`) values with literal top and bottom
preserved, and has relative prefix preservation (`normalizeT_prefix`).  Both same-grade fibres on
source profiles compose with it (`exists_private_lift_normalized`,
`exists_request_lift_normalized`).

**The supported decoding contract with terminal-block top** (`exists_terminal_decoding`): for
any admissible state, choose a fresh limit block floor `λ` above every proper value of the source
vector and above a prescribed prefix cut, and `β = λ + j`; capping at `β` (`capWitness`, a
bottom-reflecting witness through `j`) gives an admissible **proper** state with the same prefix
below the cut; the reviewer's right-filled decoder reads its normalization back exactly
(`decode_normalize`), and collapsing the **whole** terminal block and everything above to top
(`collapseBlock`, a bottom-reflecting witness through `j` because it acts on whole blocks:
`collapseBlock_witness`) recovers the original vector literally, tops included.  The composite
outgoing map is one normalized witness through `j` (`Witness.comp_of_bottom_reflecting`).  A
jump only at the endpoint `β` would not commute with replacement on the short strip below `β`;
whole-block collapse does.  Normalization itself does not retain a top-valued prescription
literally; the fibre retained it before coding and the decoder reads it back. -/

namespace VaughtConjecture.Knight

open  Value ExtOrd 

/-! ## Order facts about limit block floors -/

/-- Below a limit block floor, replacement stays below it. -/
theorem evr_lt_of_lt_limit {l} (hl : limitPart l = l) {x}
    (hx : x < ofOrd l) k i : extVisibilityReplace x k i < ofOrd l := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · simp_all
  · exact absurd hx not_top_lt
  · rw [extVisibilityReplace_ofOrd]
    unfold visibilityReplace
    split_ifs with hf
    · 
      rw [ofOrd_lt_ofOrd] at hx ⊢
      have h1 : limitPart α < limitPart l := by
        grind [limitPart_le]
      exact (((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 i)).trans_le
        (limitPart_add_omega0_le h1)).trans_le hl.le
    · exact hx

/-- Above a limit block floor, replacement stays above it. -/
theorem le_evr_of_limit_le {l} (hl : limitPart l = l) {x}
    (hx : ofOrd l ≤ x) k i : ofOrd l ≤ extVisibilityReplace x k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · simp_all
  · simp_all
  · rw [extVisibilityReplace_ofOrd]
    unfold visibilityReplace
    split_ifs with hf
    · 
      rw [ofOrd_le_ofOrd] at hx ⊢
      have h1 : l ≤ limitPart α := by rw [← hl]; exact limitPart_mono hx
      exact h1.trans le_self_add
    · exact hx

/-! ## Two elementary witnesses -/

/-- Capping at a `j`-visible positive value is a bottom-reflecting witness through `j`. -/
theorem capWitness {j} {β} (hβ : SelfVis j β) (hβbot : β ≠ ⊥) :
    Witness (gTop j) (fun x => min x β) where
  anti := (witness_id).anti
  vis := (witness_id).vis
  bot := min_bot_left _
  mono := fun _ _ h => min_le_min_right _ h
  clause5 := by
    intro x kk hle i hi
    by_cases hkk : kk ≤ j
    · exact (evr_min_of_selfVis hβ hkk hi x).symm
    · rw [gTop_of_gt (not_le.mp hkk), le_bot_iff] at hle
      have hx : x = ⊥ := (min_eq_bot.mp hle).resolve_right hβbot
      rw [hx, extVisibilityReplace_bot, min_bot_left, extVisibilityReplace_bot]

theorem capWitness_reflects_bottom {β : ExtOrd} (hβbot : β ≠ ⊥) (x : ExtOrd)
    (h : min x β = ⊥) : x = ⊥ := (min_eq_bot.mp h).resolve_right hβbot

/-- Collapse a whole terminal block and everything above it to top. -/
noncomputable def collapseBlock l x :=
  if ofOrd l ≤ x then ⊤ else x

theorem collapseBlock_of_le {l} {x} (h : ofOrd l ≤ x) :
    collapseBlock l x = ⊤ := by
  unfold collapseBlock; rw [ite_eq_left h]

theorem collapseBlock_of_lt {l} {x} (h : x < ofOrd l) :
    collapseBlock l x = x := by
  unfold collapseBlock; rw [ite_eq_right (not_le.mpr h)]

theorem collapseBlock_reflects_bottom l x (h : collapseBlock l x = ⊥) :
    x = ⊥ := by simp_all [collapseBlock] <;> aesop

/-- Whole-block collapse at a limit floor is a witness through every grade. -/
theorem collapseBlock_witness j {l} (hl : limitPart l = l) :
    Witness (gTop j) (collapseBlock l) where
  anti := (witness_id).anti
  vis := (witness_id).vis
  bot := collapseBlock_of_lt (bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _))
  mono := by
    intro x y hxy
    by_cases hx : ofOrd l ≤ x
    · rw [collapseBlock_of_le hx, collapseBlock_of_le (hx.trans hxy)]
    · rw [collapseBlock_of_lt (not_le.mp hx)]
      by_cases hy : ofOrd l ≤ y
      · rw [collapseBlock_of_le hy]; exact le_top
      · rw [collapseBlock_of_lt (not_le.mp hy)]; exact hxy
  clause5 := by
    intro x kk hle i hi
    by_cases hx : ofOrd l ≤ x
    · rw [collapseBlock_of_le hx, collapseBlock_of_le (le_evr_of_limit_le hl hx kk i),
        extVisibilityReplace_top]
    · rw [collapseBlock_of_lt (not_le.mp hx),
        collapseBlock_of_lt (evr_lt_of_lt_limit hl (not_le.mp hx) kk i)]

/-- Readback: collapsing the terminal block after capping at `β ≥ λ` recovers every value below
`λ` and literal top. -/
theorem collapseBlock_min {l} {β x} (hβ : ofOrd l ≤ β)
    (hx : x < ofOrd l ∨ x = ⊤) : collapseBlock l (min x β) = x := by
  rcases hx with hx | rfl
  · grind [collapseBlock_of_lt]
  · simp_all [collapseBlock_of_le]


