module

public import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ChoiceCountSystem

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Explicit counts for basic-factor choices

This module solves the coordinate-count system and relates its solution to the
label-count and multinomial choice spaces.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/--
Establishes the identity `q + formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2)
+ e (1 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_total_add_mixed_eq_coord_sum
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    q + formalLogOnePlusProductArgumentMixedChoiceCount q l =
      e (0 : Fin 2) + e (1 : Fin 2) := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨hleft, hright, htotal⟩
  omega

/-- Proves the bound `q ≤ e (0 : Fin 2) + e (1 : Fin 2)`. -/
theorem formalLogOnePlusProductArgument_choiceCounts_q_le_coord_sum
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    q ≤ e (0 : Fin 2) + e (1 : Fin 2) := by
  have hsum :=
    formalLogOnePlusProductArgument_choiceCounts_total_add_mixed_eq_coord_sum
      hl hbasic
  omega

/--
Establishes the identity `formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2) + e
(1 : Fin 2) - q`.
-/
theorem formalLogOnePlusProductArgument_mixedChoiceCount_eq_coord_sum_sub_q
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentMixedChoiceCount q l =
      e (0 : Fin 2) + e (1 : Fin 2) - q := by
  have hsum :=
    formalLogOnePlusProductArgument_choiceCounts_total_add_mixed_eq_coord_sum
      hl hbasic
  omega

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l = q - e (1 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_leftChoiceCount_eq_q_sub_right_coord
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentLeftChoiceCount q l =
      q - e (1 : Fin 2) := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨_hleft, hright, htotal⟩
  omega

/--
Establishes the identity `formalLogOnePlusProductArgumentRightChoiceCount q l = q - e (0 : Fin
2)`.
-/
theorem formalLogOnePlusProductArgument_rightChoiceCount_eq_q_sub_left_coord
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentRightChoiceCount q l =
      q - e (0 : Fin 2) := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨hleft, _hright, htotal⟩
  omega

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l = q - e (1 : Fin 2) ∧
formalLogOnePlusProductArgumentRightChoiceCount q l = q - e (0 : Fin 2) ∧
formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2) + e (1 : Fin 2) - q`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_explicit
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentLeftChoiceCount q l =
          q - e (1 : Fin 2) ∧
      formalLogOnePlusProductArgumentRightChoiceCount q l =
          q - e (0 : Fin 2) ∧
        formalLogOnePlusProductArgumentMixedChoiceCount q l =
          e (0 : Fin 2) + e (1 : Fin 2) - q := by
  exact
    ⟨formalLogOnePlusProductArgument_leftChoiceCount_eq_q_sub_right_coord
        hl hbasic,
      formalLogOnePlusProductArgument_rightChoiceCount_eq_q_sub_left_coord
        hl hbasic,
      formalLogOnePlusProductArgument_mixedChoiceCount_eq_coord_sum_sub_q
        hl hbasic⟩

/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 = q - e (1 :
Fin 2) ∧ formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 = q - e (0 : Fin 2) ∧
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 = e (0 : Fin 2) + e (1 : Fin 2) - q`.
-/
theorem formalLogOnePlusProductArgument_labelCounts_explicit
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 =
          q - e (1 : Fin 2) ∧
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 =
          q - e (0 : Fin 2) ∧
        formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 =
          e (0 : Fin 2) + e (1 : Fin 2) - q := by
  rcases formalLogOnePlusProductArgument_choiceCounts_explicit
      hl hbasic with ⟨hleft, hright, hmixed⟩
  exact
    ⟨by
      rw [← formalLogOnePlusProductArgument_leftChoiceCount_eq_labelCount_zero]
      exact hleft,
    by
      rw [← formalLogOnePlusProductArgument_rightChoiceCount_eq_labelCount_one]
      exact hright,
    by
      rw [←
        formalLogOnePlusProductArgument_mixedChoiceCount_eq_labelCount_two
          hbasic]
      exact hmixed⟩

/-- Every basic-factor choice satisfies the corresponding three label-count constraints. -/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_subset_labelCountChoices
    (q : ℕ) (e : Fin 2 →₀ ℕ) :
    formalLogOnePlusProductArgumentBasicFactorChoices q e ⊆
      formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e := by
  intro l hl
  rw [mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices]
  rw [mem_formalLogOnePlusProductArgumentBasicFactorChoices] at hl
  have hprod :
      l ∈ formalLogOnePlusProductArgumentBasicFactorProductChoices q := by
    rw [mem_formalLogOnePlusProductArgumentBasicFactorProductChoices]
    simp_all
  exact
    ⟨hprod,
      formalLogOnePlusProductArgument_labelCounts_explicit hl.1 hl.2⟩
