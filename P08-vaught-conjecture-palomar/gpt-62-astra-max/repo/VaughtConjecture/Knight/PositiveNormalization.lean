/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import VaughtConjecture.Knight.WitnessAlgebra
public import VaughtConjecture.Knight.NormalForm

/-! # Composition by bottom-reflecting normalized witnesses -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-- A normalized witness may be followed by a normalized, bottom-reflecting
witness at a larger grade. Bottom reflection is used only above the inner grade. -/
theorem Witness.comp_of_bottom_reflecting
    {m K : ℕ} {τ ν : ExtOrd → ExtOrd}
    (hτ : Witness (gTop m) τ) (hν : Witness (gTop K) ν)
    (hmK : m ≤ K) (hbot : ∀ x, ν x = ⊥ → x = ⊥) :
    Witness (gTop m) (ν ∘ τ) where
  anti := hτ.anti
  vis := hτ.vis
  bot := by simp only [Function.comp_apply, hτ.bot, hν.bot]
  mono := hν.mono.comp hτ.mono
  clause5 := by
    intro x k hact i hi
    change ν (τ (extVisibilityReplace x k i)) =
      extVisibilityReplace (ν (τ x)) k i
    by_cases hk : k ≤ m
    · rw [hτ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi,
        hν.clause5 (τ x) k (by rw [gTop_of_le (hk.trans hmK)]; exact le_top) i hi]
    · have hz : ν (τ x) = ⊥ := by
        apply le_bot_iff.mp
        simpa only [Function.comp_apply, gTop_of_gt (not_le.mp hk)] using hact
      have ht : τ x = ⊥ := hbot _ hz
      rw [hτ.clause5 x k (by rw [ht]; exact bot_le) i hi,
        ht, extVisibilityReplace_bot, hν.bot, extVisibilityReplace_bot]

/-- The two existing names for the normalized suppressor have the same definition. -/
theorem Transform.IsStepShifter.normalizedWitness {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hν : IsStepShifter K ν) : Witness (gTop K) ν where
  anti := (witness_id K).anti
  vis := (witness_id K).vis
  bot := hν.map_bot
  mono := hν.mono
  clause5 := by
    intro x k hact i hi
    exact hν.clause5 x k hact i hi

/-- Transport one actual controller locality, after normalizing its witness.
The semantic source row is unchanged. -/
theorem map_capped_locality_of_bottom_reflecting
    {X : Type*} {grade : X → ℕ} {E p : X → ExtOrd} {c : X}
    {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hmax : ∀ d, grade d ≤ grade c) (hcK : grade c ≤ K)
    (hvis : SelfVis (grade c) (p c))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c)))
    (hν : Witness (gTop K) ν) (hbot : ∀ x, ν x = ⊥ → x = ⊥) :
    TransformsTo grade E (fun d => min (ν (p d)) (ν (p c))) := by
  obtain ⟨τ, hτ, _, hread⟩ := exists_bounded_exact_capped_witness hmax hvis hloc
  apply (hτ.comp_of_bottom_reflecting hν hcK hbot).transformsTo
  intro d
  simp only [Function.comp_apply, gTop_of_le (hmax d), min_top_right]
  rw [hread d, hν.mono.map_min]

open Classical in
/-- The ordinal carried by a label (`0` at the endpoints). -/
noncomputable def ordOf (x : ExtOrd) : Ordinal.{0} :=
  if h : ∃ s : Ordinal.{0}, x = ofOrd s then h.choose else 0

theorem ordOf_ofOrd (s : Ordinal.{0}) : ordOf (ofOrd s) = s := by
  have h : ∃ t : Ordinal.{0}, ofOrd s = ofOrd t := ⟨s, rfl⟩
  unfold ordOf
  rw [dite_eq_left h]
  exact (ofOrd_inj.mp h.choose_spec).symm

end VaughtConjecture.Knight
