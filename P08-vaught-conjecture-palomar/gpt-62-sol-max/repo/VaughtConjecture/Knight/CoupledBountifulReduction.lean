/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedLocalityRecoding
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.Domain
public import VaughtConjecture.Knight.OnePointSuccessor
public import Mathlib.Tactic.DeriveFintype

public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.RowReadback
public import VaughtConjecture.Knight.WitnessSplice
public import VaughtConjecture.Knight.Type
public import VaughtConjecture.Knight.WitnessAlgebra

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd

open CellScheme.restrictFace (toCell belowMap pushGraded)

section StepLimit

open Classical in
/-- The two-valued shifter: `c₀` below the limit cutoff `ω·n`, `c₁` from it on. -/
noncomputable def stepShifter (n : ℕ) (c₀ c₁ : ExtOrd) : ExtOrd → ExtOrd :=
  fun a => if a = ⊥ then ⊥ else if a < ofOrd (Ordinal.omega0 * (n : Ordinal)) then c₀ else c₁

theorem stepShifter_bot (n : ℕ) (c₀ c₁ : ExtOrd) : stepShifter n c₀ c₁ ⊥ = ⊥ := rfl

theorem stepShifter_of_lt {n : ℕ} {c₀ c₁ a : ExtOrd} (ha : a ≠ ⊥)
    (h : a < ofOrd (Ordinal.omega0 * (n : Ordinal))) : stepShifter n c₀ c₁ a = c₀ := by
  classical
  unfold stepShifter; lia

theorem stepShifter_of_ge {n : ℕ} {c₀ c₁ a : ExtOrd}
    (h : ofOrd (Ordinal.omega0 * (n : Ordinal)) ≤ a) : stepShifter n c₀ c₁ a = c₁ := by
  classical
  unfold stepShifter
  aesop

theorem limitPart_omega_mul (n : ℕ) : limitPart (Ordinal.omega0 * (n : Ordinal)) =
    Ordinal.omega0 * (n : Ordinal) := by
  have := limitPart_mul_add n 0
  aesop

/-- Visibility replacement never crosses a limit cutoff, in either direction. -/
theorem evr_lt_limit {n : ℕ} {a : ExtOrd} (h : a < ofOrd (Ordinal.omega0 * (n : Ordinal)))
    (k i : ℕ) :
    extVisibilityReplace a k i < ofOrd (Ordinal.omega0 * (n : Ordinal)) := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · assumption
  · assumption
  · rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
    have hα := ofOrd_lt_ofOrd.mp h
    have hl : limitPart (visibilityReplace α k i) < limitPart (Ordinal.omega0 * (n : Ordinal)) := by
      rw [limitPart_visibilityReplace, limitPart_omega_mul]
      exact lt_of_le_of_lt (limitPart_le α) hα
    exact lt_of_lt_of_le (lt_limitPart_of_limitPart_lt hl) (limitPart_le _)

theorem evr_ge_limit {n : ℕ} {a : ExtOrd} (h : ofOrd (Ordinal.omega0 * (n : Ordinal)) ≤ a)
    (k i : ℕ) :
    ofOrd (Ordinal.omega0 * (n : Ordinal)) ≤ extVisibilityReplace a k i := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · assumption
  · assumption
  · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
    have hα := ofOrd_le_ofOrd.mp h
    calc Ordinal.omega0 * (n : Ordinal) = limitPart (Ordinal.omega0 * (n : Ordinal)) :=
          (limitPart_omega_mul n).symm
      _ ≤ limitPart α := limitPart_mono hα
      _ = limitPart (visibilityReplace α k i) := (limitPart_visibilityReplace α k i).symm
      _ ≤ visibilityReplace α k i := limitPart_le _

/-- **The step witness at a limit cutoff**: unconditional in the values (the bottom fibre is
allowed), because visibility replacement never crosses a limit. -/
theorem Witness.stepLimit (K n : ℕ) {c₀ c₁ : ExtOrd} (h : c₀ ≤ c₁) (hc₀ : SelfVis K c₀)
    (hc₁ : SelfVis K c₁) : Witness (gTop K) (stepShifter n c₀ c₁) where
  anti := (witness_id K).anti
  vis := (witness_id K).vis
  bot := stepShifter_bot n c₀ c₁
  mono := by
    intro a b hab
    by_cases ha : a = ⊥
    · rw [ha, stepShifter_bot]; exact bot_le
    grind +locals
  clause5 := by
    intro α k hk i hi
    by_cases hα : α = ⊥
    · aesop
    have hα' : extVisibilityReplace α k i ≠ ⊥ := extVisibilityReplace_ne_bot hα k i
    by_cases hkK : k ≤ K
    · by_cases hal : α < ofOrd (Ordinal.omega0 * (n : Ordinal))
      · rw [stepShifter_of_lt hα hal, stepShifter_of_lt hα' (evr_lt_limit hal k i),
          evr_eq_self_of_selfVis (hc₀.mono hkK)]
      · rw [stepShifter_of_ge (not_lt.mp hal), stepShifter_of_ge (evr_ge_limit (not_lt.mp hal) k i),
          evr_eq_self_of_selfVis (hc₁.mono hkK)]
    · rw [gTop_of_gt (by omega)] at hk
      have hσ := le_bot_iff.mp hk
      by_cases hal : α < ofOrd (Ordinal.omega0 * (n : Ordinal))
      · rw [stepShifter_of_lt hα hal] at hσ
        rw [stepShifter_of_lt hα hal, stepShifter_of_lt hα' (evr_lt_limit hal k i), hσ,
          extVisibilityReplace_bot]
      · rw [stepShifter_of_ge (not_lt.mp hal)] at hσ
        rw [stepShifter_of_ge (not_lt.mp hal), stepShifter_of_ge (evr_ge_limit (not_lt.mp hal) k i),
          hσ, extVisibilityReplace_bot]

end StepLimit

end VaughtConjecture.Knight
