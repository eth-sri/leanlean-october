/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SeparatedGradeOneCoding
public import VaughtConjecture.Knight.MixedGradeInterpolation
public import VaughtConjecture.Knight.FreeDiagonal

/-! # A finite family of source slots for an independent grade-one reading

Old source values are ranked once, before any output labels are supplied.
Their nonbottom codes occupy even blocks; odd blocks provide fresh slots.
Every source-ordered old target and every visible fresh target fit one slot.
An explicit finite maximum of step witnesses decodes all targets literally.
Bottom, top, and ties are allowed. There is no composition of transformations.

These are row templates, not jointly consistent controllers. Simultaneous
family incidences, availability, and reference readback remain separate.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.FreshSourceSlots

open Transform Value ExtOrd SeparatedGradeOne

local notation "band" => SeparatedGradeOne.band

theorem band_lt {m n : ℕ} (h : m < n) : band m < band n :=
  ofOrd_lt_ofOrd.mpr ((code_add_lt_mul (Nat.cast_lt.mpr h) 1).trans_le le_self_add)

theorem band_le_iff (m n : ℕ) : band m ≤ band n ↔ m ≤ n := by
  constructor
  · intro h
    by_contra hn
    exact (not_le_of_gt (band_lt (not_le.mp hn))) h
  · exact band_mono

noncomputable def source : Option ℕ → ExtOrd
  | none => ⊥
  | some n => band n

theorem step_band (m n : ℕ) (v : ExtOrd) :
    stepShifter m ⊥ v (band n) = if m ≤ n then v else ⊥ := by
  classical
  by_cases h : m ≤ n
  · rw [ite_eq_left h]
    apply stepShifter_of_ge
    exact ofOrd_le_ofOrd.mpr ((mul_le_mul_right (Nat.cast_le.mpr h) _).trans le_self_add)
  · rw [ite_eq_right h]
    apply stepShifter_of_lt (ofOrd_ne_bot _)
    exact ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (not_le.mp h)) 1)

section Decoder

variable {X : Type*} [Fintype X]

noncomputable def decoder (r : X → Option ℕ) (t : X → ExtOrd) (x : ExtOrd) : ExtOrd :=
  Finset.univ.sup fun d => match r d with
    | none => ⊥
    | some n => stepShifter n ⊥ (t d) x

theorem decoder_witness (r : X → Option ℕ) (t : X → ExtOrd)
    (hv : ∀ d, SelfVis 1 (t d)) : Witness (gTop 1) (decoder r t) := by
  apply Witness.finset_sup (MixedGradeInterpolation.zero_witness 1)
  intro d _
  cases h : r d with
  | none => simpa only [h] using MixedGradeInterpolation.zero_witness 1
  | some n =>
    simpa only [h] using Witness.stepLimit 1 n bot_le (selfVis_bot 1) (hv d)

theorem decoder_read (r : X → Option ℕ) (t : X → ExtOrd)
    (horder : ∀ d e, source (r d) ≤ source (r e) → t d ≤ t e)
    (hbot : ∀ d, r d = none → t d = ⊥) (d : X) : decoder r t (source (r d)) = t d := by
  classical
  cases hd : r d with
  | none =>
    simp only [source, decoder, hbot d hd]
    apply le_antisymm _ bot_le
    apply Finset.sup_le
    intro e _
    cases r e <;> simp only [stepShifter_bot, le_refl]
  | some n =>
    change decoder r t (band n) = t d
    apply le_antisymm
    · apply Finset.sup_le
      intro e _
      cases he : r e with
      | none => exact bot_le
      | some m =>
        change stepShifter m ⊥ (t e) (band n) ≤ t d
        rw [step_band]
        split_ifs with h
        · exact horder e d (by rw [he, hd]; exact band_mono h)
        · exact bot_le
    · have h := Finset.le_sup (s := Finset.univ)
        (f := fun e => match r e with
          | none => (⊥ : ExtOrd)
          | some m => stepShifter m ⊥ (t e) (band n)) (Finset.mem_univ d)
      simpa only [hd, step_band, le_refl, ↓reduceIte, decoder] using h

end Decoder

section Slots

variable {X : Type*} [Fintype X]

open Classical in
/-- Rank counts occurrences, not a quotient. Equal old values still get equal ranks. -/
noncomputable def rank (E : X → ExtOrd) (d : X) : ℕ :=
  (Finset.univ.filter fun e => E e < E d).card

theorem rank_mono {E : X → ExtOrd} {d e : X} (h : E d ≤ E e) : rank E d ≤ rank E e := by
  classical
  apply Finset.card_le_card
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.trans_le h⟩

theorem rank_strict {E : X → ExtOrd} {d e : X} (h : E d < E e) : rank E d < rank E e := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.trans h⟩
  · intro heq
    have hd : d ∈ Finset.univ.filter (fun a => E a < E e) := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h
    rw [← heq] at hd
    exact (lt_irrefl (E d)) (Finset.mem_filter.mp hd).2

theorem rank_le_iff (E : X → ExtOrd) (d e : X) : rank E d ≤ rank E e ↔ E d ≤ E e := by
  constructor
  · intro h
    by_contra hn
    exact (not_le_of_gt (rank_strict (not_le.mp hn))) h
  · exact rank_mono

theorem rank_lt_card (E : X → ExtOrd) (d : X) : rank E d < Fintype.card X := by
  classical
  change (Finset.univ.filter fun e => E e < E d).card < Finset.univ.card
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have hd : d ∈ Finset.univ.filter (fun e => E e < E d) := heq.symm ▸ Finset.mem_univ d
  exact (lt_irrefl (E d)) (Finset.mem_filter.mp hd).2

end Slots

end VaughtConjecture.Knight.FreshSourceSlots
