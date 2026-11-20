module

public import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ChoiceCountSystem

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Explicit counts for basic-factor choices

This module solves the coordinate-count system and relates its solution to the
label-count and multinomial choice spaces.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

section

variable {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q, formalLogOnePlusProductArgumentBasicFactor (l i))

include hl hbasic in
/--
Establishes the identity `q + formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2)
+ e (1 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_total_add_mixed_eq_coord_sum :
    q + formalLogOnePlusProductArgumentMixedChoiceCount q l =
      e (0 : Fin 2) + e (1 : Fin 2) := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨hleft, hright, htotal⟩
  calc
    _ =
        (formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
            formalLogOnePlusProductArgumentMixedChoiceCount q l := (congrArg
        (fun t : ℕ => t + formalLogOnePlusProductArgumentMixedChoiceCount q l)
        htotal).symm
    _ =
        (formalLogOnePlusProductArgumentLeftChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
        (formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) := by
      omega
    _ = e (0 : Fin 2) + e (1 : Fin 2) := by
      omega

include hl hbasic in
/-- Proves the bound `q ≤ e (0 : Fin 2) + e (1 : Fin 2)`. -/
theorem formalLogOnePlusProductArgument_choiceCounts_q_le_coord_sum :
    q ≤ e (0 : Fin 2) + e (1 : Fin 2) := by
  exact Nat.le.intro (formalLogOnePlusProductArgument_choiceCounts_total_add_mixed_eq_coord_sum hl hbasic)

include hl hbasic in
/--
Establishes the identity `formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2) + e
(1 : Fin 2) - q`.
-/
theorem formalLogOnePlusProductArgument_mixedChoiceCount_eq_coord_sum_sub_q :
    formalLogOnePlusProductArgumentMixedChoiceCount q l =
      e (0 : Fin 2) + e (1 : Fin 2) - q := by
  calc
    formalLogOnePlusProductArgumentMixedChoiceCount q l =
        q + formalLogOnePlusProductArgumentMixedChoiceCount q l - q := by
      simp
    _ = e (0 : Fin 2) + e (1 : Fin 2) - q := by
      rw [(formalLogOnePlusProductArgument_choiceCounts_total_add_mixed_eq_coord_sum
        hl hbasic)]

include hl hbasic in
/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l = q - e (1 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_leftChoiceCount_eq_q_sub_right_coord :
    formalLogOnePlusProductArgumentLeftChoiceCount q l =
      q - e (1 : Fin 2) := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨_hleft, hright, htotal⟩
  let e₀ := e (1 : Fin 2)
  have hq :
      e₀ +
          formalLogOnePlusProductArgumentLeftChoiceCount q l =
        q := by
    calc
      _ =
        (formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
            formalLogOnePlusProductArgumentLeftChoiceCount q l := by
        rw [hright]
      _ =
        formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l := by
        simp only [Nat.add_left_comm, Nat.add_comm]
      _ = q := htotal
  calc
    formalLogOnePlusProductArgumentLeftChoiceCount q l =
        e₀ +
            formalLogOnePlusProductArgumentLeftChoiceCount q l -
          e₀ := by
      simp
    _ = q - e₀ := by
      rw [hq]

include hl hbasic in
/--
Establishes the identity `formalLogOnePlusProductArgumentRightChoiceCount q l = q - e (0 : Fin
2)`.
-/
theorem formalLogOnePlusProductArgument_rightChoiceCount_eq_q_sub_left_coord :
    formalLogOnePlusProductArgumentRightChoiceCount q l =
      q - e (0 : Fin 2) := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨hleft, _hright, htotal⟩
  let e₀ := e (0 : Fin 2)
  have hq :
      e₀ +
          formalLogOnePlusProductArgumentRightChoiceCount q l =
        q := by
    calc
      _ =
        (formalLogOnePlusProductArgumentLeftChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
            formalLogOnePlusProductArgumentRightChoiceCount q l := by
        rw [hleft]
      _ =
        formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l := by
        simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = q := htotal
  calc
    formalLogOnePlusProductArgumentRightChoiceCount q l =
        e₀ +
            formalLogOnePlusProductArgumentRightChoiceCount q l -
          e₀ := by
      simp
    _ = q - e₀ := by
      rw [hq]

include hl hbasic in
/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l = q - e (1 : Fin 2) ∧
formalLogOnePlusProductArgumentRightChoiceCount q l = q - e (0 : Fin 2) ∧
formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2) + e (1 : Fin 2) - q`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_explicit :
    formalLogOnePlusProductArgumentLeftChoiceCount q l =
          q - e (1 : Fin 2) ∧
      formalLogOnePlusProductArgumentRightChoiceCount q l =
          q - e (0 : Fin 2) ∧
        formalLogOnePlusProductArgumentMixedChoiceCount q l =
          e (0 : Fin 2) + e (1 : Fin 2) - q := ⟨formalLogOnePlusProductArgument_leftChoiceCount_eq_q_sub_right_coord
        hl hbasic,
      formalLogOnePlusProductArgument_rightChoiceCount_eq_q_sub_left_coord
        hl hbasic,
      formalLogOnePlusProductArgument_mixedChoiceCount_eq_coord_sum_sub_q
        hl hbasic⟩

include hl hbasic in
/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 = q - e (1 :
Fin 2) ∧ formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 = q - e (0 : Fin 2) ∧
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 = e (0 : Fin 2) + e (1 : Fin 2) - q`.
-/
theorem formalLogOnePlusProductArgument_labelCounts_explicit :
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

end

/-- Every basic-factor choice satisfies the corresponding three label-count constraints. -/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_subset_labelCountChoices
    (q : ℕ) (e : Fin 2 →₀ ℕ) :
    formalLogOnePlusProductArgumentBasicFactorChoices q e ⊆
      formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e := by
  intro l hl
  rw [mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices]
  rw [mem_formalLogOnePlusProductArgumentBasicFactorChoices] at hl
  refine
    ⟨?_,
      formalLogOnePlusProductArgument_labelCounts_explicit hl.1 hl.2⟩
  rw [mem_formalLogOnePlusProductArgumentBasicFactorProductChoices]
  exact ⟨(Finset.mem_finsuppAntidiag.mp hl.1).2, hl.2⟩

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
