/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WitnessAlgebra
public import VaughtConjecture.Knight.Type
public import VaughtConjecture.Knight.PartialSections
public import VaughtConjecture.Knight.WitnessSplice
public import VaughtConjecture.Knight.PullbackSemantics
public import VaughtConjecture.Knight.RowReadback
public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.Domain
public import VaughtConjecture.Knight.OnePointSuccessor
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.CappedCore

/-! # Bountifulness of the coupled semantics, reduced by scope

The three modified rows of `rows₃` are frozen.  **The reduction** (`rows₃_isBountiful_of`):
bountifulness (Def. 2.5.14) of `rows₃` follows from the **scope-changing obligation at grades
at most three** (`ProperToFull₃Low`: a proper pair below `(univ, j)`, `j ≤ 3`).  The cases with a
proper target pair are the fixed glue's (`bountiful₂_A`, `bountiful₂_B`): every row in a proper
lower set is unchanged (`respects₃_iff_of_proper`).  The full-scope pairs are the general
full-scope extension (`bountiful_full_scope`), and grade four reduces to grade three exactly as
for the fixed glue.  Under the obligation the coupled domain is a `SemScheme`
(`semSchemeCoupled`).

**The smallest remaining case, grade one** (`(C, 1)` below `(univ, 1)`, `C` proper): the
constraints a respecting labelling `q` of `(univ, 1)` must satisfy, extracted from actual
respecting inputs — the separation deliberately breaks the old glue's controller-probe
equalities and creates new ones:
* every label is at most the controller's (`le_U_H_of_respects`; the controller `U_H` is the
  unique cell of graded index `(univ, 1)`, `eq_U_H_of_cell`);
* **the new probe equality** `q H₀new = q U_H` (`H₀new_eq_U_H_of_respects`): the copy and the
  diagonal read the same separating source `ω·2+2` at the controller — in the fixed glue the
  three occurrences were identified, now the copy is tied to the controller instead;
* **the clause-5 coupling at the bottom label** (`U_H_eq_bot_of_H₀old`): the old occurrence's
  source `ω·2+1` and the separating source `ω·2+2` sit in one `ω`-block one step apart, so a
  shifter sending the first to `⊥` sends the second to `⊥`: `q H₀old = ⊥ → q U_H = ⊥`.  A
  retuning rule choosing the controller's label freely above a bottom old label is refuted by
  this constraint alone.

**A witness for the retuning** (`Witness.stepLimit`): the two-valued shifter `c₀` below a
*limit* cutoff `ω·n`, `c₁` from it on, is a witness unconditionally in the values (the bottom
fibre allowed), because visibility replacement never crosses a limit (`evr_lt_limit`,
`evr_ge_limit`) — the modification `Witness.raise`/`Witness.lower` cannot express (their cutoff
needs finite part above the threshold).  It is the witness at the level-one witness rows (sources
`ω+1` at the proper cells, `ω·2+1` at the diagonal), where the free labels at the proper cells
and at the old occurrence are chosen independently.

Not done: the obligation `ProperToFull₃Low` itself (the retuning at grades one to three).
Construction-private (not root-exported). -/
@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

/-! ## The smallest scope-changing case: grade one -/

/-! ## A step witness at a limit cutoff -/

section StepLimit

open Classical in
/-- The two-valued shifter: `c₀` below the limit cutoff `ω·n`, `c₁` from it on. -/
noncomputable def stepShifter (n : ℕ) (c₀ c₁ : ExtOrd) : ExtOrd → ExtOrd :=
  fun a => if a = ⊥ then ⊥ else if a < ofOrd (Ordinal.omega0 * (n : Ordinal)) then c₀ else c₁

theorem stepShifter_bot (n : ℕ) (c₀ c₁ : ExtOrd) : stepShifter n c₀ c₁ ⊥ = ⊥ := by
  classical
  unfold stepShifter; rw [ite_eq_left rfl]
theorem stepShifter_of_lt {n : ℕ} {c₀ c₁ a : ExtOrd} (ha : a ≠ ⊥)
    (h : a < ofOrd (Ordinal.omega0 * (n : Ordinal))) : stepShifter n c₀ c₁ a = c₀ := by
  classical
  unfold stepShifter; rw [ite_eq_right ha, ite_eq_left h]
theorem stepShifter_of_ge {n : ℕ} {c₀ c₁ a : ExtOrd}
    (h : ofOrd (Ordinal.omega0 * (n : Ordinal)) ≤ a) : stepShifter n c₀ c₁ a = c₁ := by
  classical
  unfold stepShifter
  rw [ite_eq_right (fun hb => not_ofOrd_le_bot _ (hb ▸ h)), ite_eq_right (not_lt.mpr h)]

theorem limitPart_omega_mul (n : ℕ) : limitPart (Ordinal.omega0 * (n : Ordinal)) =
    Ordinal.omega0 * (n : Ordinal) := by
  have := limitPart_mul_add n 0
  rw [Nat.cast_zero, add_zero] at this; exact this

/-- Visibility replacement never crosses a limit cutoff, in either direction. -/
theorem evr_lt_limit {n : ℕ} {a : ExtOrd} (h : a < ofOrd (Ordinal.omega0 * (n : Ordinal)))
    (k i : ℕ) :
    extVisibilityReplace a k i < ofOrd (Ordinal.omega0 * (n : Ordinal)) := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · rw [extVisibilityReplace_bot]; exact bot_lt_ofOrd _
  · exact absurd h (not_lt.mpr le_top)
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
  · exact absurd h (not_ofOrd_le_bot _)
  · rw [extVisibilityReplace_top]; exact le_top
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
    have hb : b ≠ ⊥ := fun hb => ha (le_bot_iff.mp (hb ▸ hab))
    by_cases hal : a < ofOrd (Ordinal.omega0 * (n : Ordinal))
    · rw [stepShifter_of_lt ha hal]
      by_cases hbl : b < ofOrd (Ordinal.omega0 * (n : Ordinal))
      · rw [stepShifter_of_lt hb hbl]
      · rw [stepShifter_of_ge (not_lt.mp hbl)]; exact h
    · have hbl : ¬ b < ofOrd (Ordinal.omega0 * (n : Ordinal)) :=
        fun hbl => hal (lt_of_le_of_lt hab hbl)
      rw [stepShifter_of_ge (not_lt.mp hal), stepShifter_of_ge (not_lt.mp hbl)]
  clause5 := by
    intro α k hk i hi
    by_cases hα : α = ⊥
    · rw [hα, stepShifter_bot, extVisibilityReplace_bot, stepShifter_bot]
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
