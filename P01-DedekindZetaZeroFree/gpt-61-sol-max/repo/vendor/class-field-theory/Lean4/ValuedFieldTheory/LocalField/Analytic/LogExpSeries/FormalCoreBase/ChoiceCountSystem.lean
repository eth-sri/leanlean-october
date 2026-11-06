module

public import Mathlib

public import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.BasicFactors

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Coordinate equations for basic-factor choices

This module derives the three coordinate and total-count equations satisfied by
a choice of the basic factors in `X + Y + XY`.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- Basic-factor sequences with the three label counts forced by `q` and the
target exponent vector `e`. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorLabelCountChoices
    (q : ℕ) (e : Fin 2 →₀ ℕ)  :=
  (formalLogOnePlusProductArgumentBasicFactorProductChoices q).filter
    (fun l =>
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 =
          q - e (1 : Fin 2) ∧
        formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 =
          q - e (0 : Fin 2) ∧
          formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 =
            e (0 : Fin 2) + e (1 : Fin 2) - q)

/--
Characterizes `l ∈ formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e` by the
equivalent condition `l ∈ formalLogOnePlusProductArgumentBasicFactorProductChoices q ∧
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 = q - e (1 : Fin 2) ∧
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 = q - e (0 : Fin 2) ∧
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 = e (0 : Fin 2) + e (1 : Fin 2) - q`.
-/
theorem mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)} :
    l ∈ formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e ↔
      l ∈ formalLogOnePlusProductArgumentBasicFactorProductChoices q ∧
        formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 =
            q - e (1 : Fin 2) ∧
          formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 =
            q - e (0 : Fin 2) ∧
            formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 =
              e (0 : Fin 2) + e (1 : Fin 2) - q := by
  classical
  simp [formalLogOnePlusProductArgumentBasicFactorLabelCountChoices]

section
variable {m : Fin 2 →₀ ℕ}
    (hm : formalLogOnePlusProductArgumentBasicFactor m)
include m hm
/--
Establishes the identity `m (0 : Fin 2) = (if m = Finsupp.single (0 : Fin 2) 1 then 1 else 0) +
(if m = Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 then 1 else 0)`.
-/
theorem formalLogOnePlusProductArgumentBasicFactor_left_coord
      :
    m (0 : Fin 2) =
      (if m = Finsupp.single (0 : Fin 2) 1 then 1 else 0) +
        (if m =
            Finsupp.single (0 : Fin 2) 1 +
              Finsupp.single (1 : Fin 2) 1
          then 1 else 0) := by
  rcases hm with hleft | hright | hmixed
  · simp [hleft]
  · have hrightLeft  :=
      finsupp_fin_two_single_left_ne_single_right.symm
    simp [hright, hrightLeft]
  · simp_all

/--
Establishes the identity `m (1 : Fin 2) = (if m = Finsupp.single (1 : Fin 2) 1 then 1 else 0) +
(if m = Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 then 1 else 0)`.
-/
theorem formalLogOnePlusProductArgumentBasicFactor_right_coord
      :
    m (1 : Fin 2) =
      (if m = Finsupp.single (1 : Fin 2) 1 then 1 else 0) +
        (if m =
            Finsupp.single (0 : Fin 2) 1 +
              Finsupp.single (1 : Fin 2) 1
          then 1 else 0) := by
  rcases hm with hleft | hright | hmixed
  · simp [hleft, finsupp_fin_two_single_left_ne_single_right]
  · simp [hright]
  · simp_all

/--
Establishes the identity `(if m = Finsupp.single (0 : Fin 2) 1 then 1 else 0) + (if m =
Finsupp.single (1 : Fin 2) 1 then 1 else 0) + (if m = Finsupp.single (0 : Fin 2) 1 +
Finsupp.single (1 : Fin 2) 1 then 1 else 0) = 1`.
-/
theorem formalLogOnePlusProductArgumentBasicFactor_total_indicator
      :
    (if m = Finsupp.single (0 : Fin 2) 1 then 1 else 0) +
          (if m = Finsupp.single (1 : Fin 2) 1 then 1 else 0) +
        (if m =
            Finsupp.single (0 : Fin 2) 1 +
              Finsupp.single (1 : Fin 2) 1
          then 1 else 0) =
      1 := by
  rcases hm with hleft | hright | hmixed
  · simp [hleft, finsupp_fin_two_single_left_ne_single_right]
  · have hrightLeft  :=
      finsupp_fin_two_single_left_ne_single_right.symm
    simp [hright, hrightLeft]
  simp_all
end


section
variable {q : ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i))
include q l hbasic
/--
Establishes the identity `(∑ i ∈ Finset.range q, l i (0 : Fin 2)) =
formalLogOnePlusProductArgumentLeftChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l`.
-/
theorem formalLogOnePlusProductArgument_leftCoord_sum_eq_choiceCounts
      :
    (∑ i ∈ Finset.range q, l i (0 : Fin 2)) =
      formalLogOnePlusProductArgumentLeftChoiceCount q l +
        formalLogOnePlusProductArgumentMixedChoiceCount q l := by
  rw [formalLogOnePlusProductArgumentLeftChoiceCount,
    formalLogOnePlusProductArgumentMixedChoiceCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply formalLogOnePlusProductArgumentBasicFactor_left_coord <;> aesop

/--
Establishes the identity `(∑ i ∈ Finset.range q, l i (1 : Fin 2)) =
formalLogOnePlusProductArgumentRightChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l`.
-/
theorem formalLogOnePlusProductArgument_rightCoord_sum_eq_choiceCounts
      :
    (∑ i ∈ Finset.range q, l i (1 : Fin 2)) =
      formalLogOnePlusProductArgumentRightChoiceCount q l +
        formalLogOnePlusProductArgumentMixedChoiceCount q l := by
  rw [formalLogOnePlusProductArgumentRightChoiceCount,
    formalLogOnePlusProductArgumentMixedChoiceCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply formalLogOnePlusProductArgumentBasicFactor_right_coord <;> aesop

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l +
formalLogOnePlusProductArgumentRightChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l = q`.
-/
theorem formalLogOnePlusProductArgument_totalChoiceCount_eq
      :
    formalLogOnePlusProductArgumentLeftChoiceCount q l +
        formalLogOnePlusProductArgumentRightChoiceCount q l +
      formalLogOnePlusProductArgumentMixedChoiceCount q l =
    q := by
  rw [formalLogOnePlusProductArgumentLeftChoiceCount,
    formalLogOnePlusProductArgumentRightChoiceCount,
    formalLogOnePlusProductArgumentMixedChoiceCount,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    (∑ i ∈ Finset.range q,
        (((if l i = Finsupp.single (0 : Fin 2) 1 then 1 else 0) +
            (if l i = Finsupp.single (1 : Fin 2) 1 then 1 else 0)) +
          (if l i =
              Finsupp.single (0 : Fin 2) 1 +
                Finsupp.single (1 : Fin 2) 1
          then 1 else 0))) =
        (∑ i ∈ Finset.range q, (1 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply formalLogOnePlusProductArgumentBasicFactor_total_indicator <;> aesop
    _ = q := by simp
end


section
variable {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i))
include q e l hl hbasic
/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_left_add_mixed_eq
      :
    formalLogOnePlusProductArgumentLeftChoiceCount q l +
      formalLogOnePlusProductArgumentMixedChoiceCount q l =
        e (0 : Fin 2) := by
  rw [← formalLogOnePlusProductArgument_leftCoord_sum_eq_choiceCounts hbasic]
  have hsum := (Finset.mem_finsuppAntidiag.mp hl).1
  simpa [Finsupp.finsetSum_apply] using
    congrArg (fun m : Fin 2 →₀ ℕ => m (0 : Fin 2)) hsum

/--
Establishes the identity `formalLogOnePlusProductArgumentRightChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l = e (1 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_right_add_mixed_eq
      :
    formalLogOnePlusProductArgumentRightChoiceCount q l +
      formalLogOnePlusProductArgumentMixedChoiceCount q l =
        e (1 : Fin 2) := by
  rw [← formalLogOnePlusProductArgument_rightCoord_sum_eq_choiceCounts hbasic]
  have hsum := (Finset.mem_finsuppAntidiag.mp hl).1
  simpa [Finsupp.finsetSum_apply] using
    congrArg (fun m : Fin 2 →₀ ℕ => m (1 : Fin 2)) hsum

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2) ∧
formalLogOnePlusProductArgumentRightChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l = e (1 : Fin 2) ∧
formalLogOnePlusProductArgumentLeftChoiceCount q l +
formalLogOnePlusProductArgumentRightChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l = q`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_system
      :
    formalLogOnePlusProductArgumentLeftChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l =
        e (0 : Fin 2) ∧
      formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l =
        e (1 : Fin 2) ∧
      formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l =
        q := ⟨formalLogOnePlusProductArgument_choiceCounts_left_add_mixed_eq
        hl hbasic,
      formalLogOnePlusProductArgument_choiceCounts_right_add_mixed_eq
        hl hbasic,
      formalLogOnePlusProductArgument_totalChoiceCount_eq hbasic⟩
end



end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
