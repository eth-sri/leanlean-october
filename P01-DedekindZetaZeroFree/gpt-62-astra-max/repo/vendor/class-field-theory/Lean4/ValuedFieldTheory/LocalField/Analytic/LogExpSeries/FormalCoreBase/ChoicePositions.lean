module

public import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ExplicitChoiceCounts

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Realizing formal-product choices by position sets

This module constructs a basic-factor choice from its mixed and left position
sets and proves the resulting position-count formulas.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- The left basic exponent vector. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorLeft :
    Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) 1

/-- The right basic exponent vector. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorRight :
    Fin 2 →₀ ℕ :=
  Finsupp.single (1 : Fin 2) 1

/-- The mixed basic exponent vector. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorMixed :
    Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1

/--
Characterizes `formalLogOnePlusProductArgumentBasicFactorLabel m = (2 : Fin 3)` by the equivalent
condition `m = formalLogOnePlusProductArgumentBasicFactorMixed`.
-/
theorem formalLogOnePlusProductArgumentBasicFactorLabel_eq_two_iff_of_basic
    {m : Fin 2 →₀ ℕ}
    (hm : formalLogOnePlusProductArgumentBasicFactor m) :
    formalLogOnePlusProductArgumentBasicFactorLabel m = (2 : Fin 3) ↔
      m = formalLogOnePlusProductArgumentBasicFactorMixed := by
  constructor
  · intro h
    rcases hm with hleft | hright | hmixed
    · simp [hleft] at h
    · simp [hright] at h
    exact hmixed
  · simp_all [formalLogOnePlusProductArgumentBasicFactorMixed]

/-- The basic-factor sequence with mixed positions `M`, left positions `L`,
and right factors in every remaining position below `q`. -/
noncomputable def formalLogOnePlusProductArgumentChoiceFromMixedLeft
    (q : ℕ) (M L : Finset ℕ) : ℕ →₀ (Fin 2 →₀ ℕ) :=
  Finsupp.onFinset (Finset.range q)
    (fun i =>
      if i ∈ Finset.range q then
        if i ∈ M then formalLogOnePlusProductArgumentBasicFactorMixed
        else if i ∈ L then formalLogOnePlusProductArgumentBasicFactorLeft
        else formalLogOnePlusProductArgumentBasicFactorRight
      else 0)
    (by
      intro i hi
      by_cases hq : i ∈ Finset.range q
      · exact hq
      · simp [hq] at hi)

section

variable {q : ℕ} {M L : Finset ℕ} {i : ℕ}

/--
Establishes the identity `formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i = if i ∈ M
then formalLogOnePlusProductArgumentBasicFactorMixed else if i ∈ L then
formalLogOnePlusProductArgumentBasicFactorLeft else
formalLogOnePlusProductArgumentBasicFactorRight`.
-/
@[simp] theorem formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem (hi : i ∈ Finset.range q) :
    formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i =
      if i ∈ M then formalLogOnePlusProductArgumentBasicFactorMixed
      else if i ∈ L then formalLogOnePlusProductArgumentBasicFactorLeft
      else formalLogOnePlusProductArgumentBasicFactorRight := by
  simp_all [formalLogOnePlusProductArgumentChoiceFromMixedLeft]

/-- Establishes the identity `formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i = 0`. -/
@[simp] theorem formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_not_mem (hi : i ∉ Finset.range q) :
    formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i = 0 := by
  simp_all [formalLogOnePlusProductArgumentChoiceFromMixedLeft]

end

section

variable (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ))

/-- Positions below `q` at which `l` has the mixed-factor label. -/
noncomputable def formalLogOnePlusProductArgumentMixedPositions : Finset ℕ :=
  (Finset.range q).filter fun i =>
    formalLogOnePlusProductArgumentBasicFactorLabel (l i) = (2 : Fin 3)

/-- Positions below `q` at which `l` has the left-factor label. -/
noncomputable def formalLogOnePlusProductArgumentLeftPositions : Finset ℕ :=
  (Finset.range q).filter fun i =>
    formalLogOnePlusProductArgumentBasicFactorLabel (l i) = (0 : Fin 3)

/-- Positions below `q` at which `l` has the right-factor label. -/
noncomputable def formalLogOnePlusProductArgumentRightPositions : Finset ℕ :=
  (Finset.range q).filter fun i =>
    formalLogOnePlusProductArgumentBasicFactorLabel (l i) = (1 : Fin 3)

/--
Establishes the identity `(formalLogOnePlusProductArgumentMixedPositions q l).card =
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2`.
-/
theorem formalLogOnePlusProductArgumentMixedPositions_card :
    (formalLogOnePlusProductArgumentMixedPositions q l).card =
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 := by
  simp [formalLogOnePlusProductArgumentMixedPositions,
    formalLogOnePlusProductArgumentBasicFactorLabelCount, Finset.sum_boole]

/--
Establishes the identity `(formalLogOnePlusProductArgumentLeftPositions q l).card =
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0`.
-/
theorem formalLogOnePlusProductArgumentLeftPositions_card :
    (formalLogOnePlusProductArgumentLeftPositions q l).card =
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 := by
  simp [formalLogOnePlusProductArgumentLeftPositions,
    formalLogOnePlusProductArgumentBasicFactorLabelCount, Finset.sum_boole]

/--
Establishes the identity `(formalLogOnePlusProductArgumentRightPositions q l).card =
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1`.
-/
theorem formalLogOnePlusProductArgumentRightPositions_card :
    (formalLogOnePlusProductArgumentRightPositions q l).card =
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 := by
  simp [formalLogOnePlusProductArgumentRightPositions,
    formalLogOnePlusProductArgumentBasicFactorLabelCount, Finset.sum_boole]

end

section

variable {q : ℕ} {M L : Finset ℕ}

/--
Establishes the identity `formalLogOnePlusProductArgumentMixedPositions q
(formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L) = M`.
-/
theorem formalLogOnePlusProductArgumentMixedPositions_choiceFromMixedLeft (hM : M ⊆ Finset.range q) :
    formalLogOnePlusProductArgumentMixedPositions q
        (formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L) = M := by
  ext i
  constructor
  · intro hi
    have hq := (Finset.mem_filter.mp hi).1
    have hlabel :=
      (Finset.mem_filter.mp hi).2
    by_cases hMi : i ∈ M
    · exact hMi
    · by_cases hLi : i ∈ L
      · simp_all [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem, hq, hMi, hLi, formalLogOnePlusProductArgumentBasicFactorLeft]
      · simp_all [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem, hq, hMi, hLi, formalLogOnePlusProductArgumentBasicFactorRight]
  · intro hMi
    simp [formalLogOnePlusProductArgumentMixedPositions, (hM hMi), hMi,
      formalLogOnePlusProductArgumentBasicFactorMixed]

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftPositions q
(formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L) = L`.
-/
theorem formalLogOnePlusProductArgumentLeftPositions_choiceFromMixedLeft (hL : L ⊆ Finset.range q \ M) :
    formalLogOnePlusProductArgumentLeftPositions q
        (formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L) = L := by
  ext i
  constructor
  · intro hi
    have hq := (Finset.mem_filter.mp hi).1
    have hlabel :=
      (Finset.mem_filter.mp hi).2
    by_cases hMi : i ∈ M
    · simp_all [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem, hq, hMi, formalLogOnePlusProductArgumentBasicFactorMixed]
    · by_cases hLi : i ∈ L
      · exact hLi
      · simp_all [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem, hq, hMi, hLi, formalLogOnePlusProductArgumentBasicFactorRight]
  · intro hLi
    simp [formalLogOnePlusProductArgumentLeftPositions, ((Finset.mem_sdiff.mp (hL hLi)).1), ((Finset.mem_sdiff.mp (hL hLi)).2), hLi,
      formalLogOnePlusProductArgumentBasicFactorLeft]

/--
Establishes the identity `formalLogOnePlusProductArgumentRightPositions q
(formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L) = Finset.range q \ (M ∪ L)`.
-/
theorem formalLogOnePlusProductArgumentRightPositions_choiceFromMixedLeft (hL : L ⊆ Finset.range q \ M) :
    formalLogOnePlusProductArgumentRightPositions q
        (formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L) =
      Finset.range q \ (M ∪ L) := by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_sdiff]
    have hq := (Finset.mem_filter.mp hi).1
    have hlabel :=
      (Finset.mem_filter.mp hi).2
    refine ⟨hq, ?_⟩
    rw [Finset.mem_union]
    intro hML
    rcases hML with hMi | hLi
    · simp_all [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem, hq, hMi, formalLogOnePlusProductArgumentBasicFactorMixed]
    · simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hq,
        ((Finset.mem_sdiff.mp (hL hLi)).2), hLi, formalLogOnePlusProductArgumentBasicFactorLeft] at hlabel
  · simp_all [Finset.mem_sdiff, formalLogOnePlusProductArgumentRightPositions, formalLogOnePlusProductArgumentBasicFactorRight]

end

/--
Establishes the identity `(formalLogOnePlusProductArgumentRightPositions q
(formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L)).card = q - a`.
-/
theorem formalLogOnePlusProductArgumentRightPositions_choiceFromMixedLeft_card
    {q a b : ℕ} {M L : Finset ℕ}
    (hMsub : M ⊆ Finset.range q) (hMcard : M.card = a + b - q)
    (hLsub : L ⊆ Finset.range q \ M) (hLcard : L.card = q - b)
    (hleft : a ≤ q) (hright : b ≤ q) (hsum : q ≤ a + b) :
    (formalLogOnePlusProductArgumentRightPositions q
      (formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L)).card =
        q - a := by
  rw [formalLogOnePlusProductArgumentRightPositions_choiceFromMixedLeft hLsub]
  have hLrange : L ⊆ Finset.range q := fun i hi =>
    (Finset.mem_sdiff.mp (hLsub hi)).1
  have hdisj : Disjoint M L := by
    rw [Finset.disjoint_left]
    intro i hMi hLi
    exact (Finset.mem_sdiff.mp (hLsub hLi)).2 hMi
  have hunionSub : M ∪ L ⊆ Finset.range q := by
    intro i hi
    rcases Finset.mem_union.mp hi with hMi | hLi
    · exact hMsub hMi
    · exact hLrange hLi
  simp [Finset.card_sdiff_of_subset hunionSub]
  rw [Finset.card_union_of_disjoint hdisj, hMcard, hLcard]
  omega

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
