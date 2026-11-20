module

public import ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.FieldTheory.Perfect
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Local fields

A local-field package here is a chosen complete discretely valued field with
finite residue field.  The topology-first mathlib class remains available
through imports; this file only adds the chosen-valuation API needed downstream.
-/

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

/-- A local field with a chosen complete discrete valuation and finite residue field. -/
structure LocalField (K : Type u) [Field K] extends CompleteDVF.{u, v} K where
  /-- The residue field of the chosen complete discrete valuation is finite. -/
  [residueFinite : Finite toCompleteDVF.residueField]

attribute [instance] LocalField.residueFinite

namespace LocalField

variable {K : Type u} [Field K]

section

variable (F : LocalField.{u, v} K)

/-- The residue field of a local field package. -/
abbrev residueField : Type u :=
  F.toCompleteDVF.residueField

/-- The valuation subring of a local field package. -/
abbrev valuationSubring : Type u :=
  F.toCompleteDVF.valuationSubring

/-- The maximal ideal of the valuation subring. -/
abbrev maximalIdeal : Ideal F.valuationSubring :=
  F.toCompleteDVF.maximalIdeal

/-- The residue map of a local field package. -/
abbrev residueMap :
    RingHom F.valuationSubring F.residueField :=
  F.toCompleteDVF.residueMap

/-- The valuation subring of a local field package is Henselian. -/
theorem henselianRing :
    HenselianRing F.valuationSubring F.maximalIdeal :=
  F.toCompleteDVF.henselianRing

/-- A local field package has a uniformizer. -/
theorem exists_uniformizer :
    ∃ pi : F.valuationSubring, F.toCompleteDVF.valuation.IsUniformizer (pi : K) :=
  F.toCompleteDVF.exists_uniformizer

/-- The residue characteristic of a local field. -/
noncomputable abbrev residueCharacteristic : ℕ :=
  ringChar F.residueField

/-- Establishes the inequality `F.residueCharacteristic ≠ 0`. -/
theorem residueCharacteristic_ne_zero :
    F.residueCharacteristic ≠ 0 :=
  CharP.ringChar_ne_zero_of_finite F.residueField

/-- Proves the primality statement `Nat.Prime F.residueCharacteristic`. -/
theorem residueCharacteristic_prime :
    Nat.Prime F.residueCharacteristic := by
  exact CharP.prime_ringChar F.toCompleteDVF.residueField

end

/-- The target has the stated characteristic: `CharP F.residueField F.residueCharacteristic`. -/
instance residueField_charP_residueCharacteristic (F : LocalField.{u, v} K) :
    CharP F.residueField F.residueCharacteristic :=
  ringChar.charP (R := F.residueField)

/-- Registers the mathematical fact `Fact F.residueCharacteristic.Prime` for typeclass inference. -/
instance residueCharacteristic.fact_prime (F : LocalField.{u, v} K) :
    Fact F.residueCharacteristic.Prime :=
  ⟨F.residueCharacteristic_prime⟩

/-- The residue characteristic vanishes after reduction modulo the maximal
ideal.  This is the first characteristic input in the converse direction of
the local-field structure theory, the local-field structure classification. -/
theorem residueCharacteristic_natCast_residue_eq_zero
    (F : LocalField.{u, v} K) :
    F.residueMap (F.residueCharacteristic : F.valuationSubring) = 0 := by
  simp

/-- The residue characteristic belongs to the maximal ideal of the valuation
ring. -/
theorem residueCharacteristic_natCast_mem_maximalIdeal
    (F : LocalField.{u, v} K) :
    (F.residueCharacteristic : F.valuationSubring) ∈ F.maximalIdeal :=
  (F.toCompleteDVF.residue_eq_zero_iff
    (F.residueCharacteristic : F.valuationSubring)).1
    F.residueCharacteristic_natCast_residue_eq_zero

/-- Valuatively, the residue characteristic lies in the open unit ball. -/
theorem valuation_residueCharacteristic_natCast_lt_one
    (F : LocalField.{u, v} K) :
    F.toCompleteDVF.valuation
      ((F.residueCharacteristic : F.valuationSubring) : K) < 1 :=
  (F.toCompleteDVF.mem_maximalIdeal_iff
    (F.residueCharacteristic : F.valuationSubring)).1
    F.residueCharacteristic_natCast_mem_maximalIdeal

/-- Field-level form of the previous valuation estimate. -/
theorem valuation_natCast_residueCharacteristic_lt_one
    (F : LocalField.{u, v} K) :
    F.toCompleteDVF.valuation (F.residueCharacteristic : K) < 1 := by
  exact F.valuation_residueCharacteristic_natCast_lt_one

/-- In mixed characteristic, the residue characteristic is a nonzero element of
the field even though it reduces to zero. -/
theorem natCast_residueCharacteristic_ne_zero_of_charZero
    (F : LocalField.{u, v} K) [CharZero K] :
    (F.residueCharacteristic : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr F.residueCharacteristic_ne_zero

/-- For an arbitrary integer, membership in the maximal ideal is exactly
divisibility by the residue characteristic. -/
theorem intCast_mem_maximalIdeal_iff_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (z : ℤ) :
    (z : F.valuationSubring) ∈ F.maximalIdeal ↔
      (F.residueCharacteristic : ℤ) ∣ z := by
  rw [← F.toCompleteDVF.residue_eq_zero_iff (z : F.valuationSubring)]
  exact CharP.intCast_eq_zero_iff F.residueField F.residueCharacteristic z

section

variable (F : LocalField.{u, v} K)

/-- Natural-number version of
`intCast_mem_maximalIdeal_iff_residueCharacteristic_dvd`. -/
theorem natCast_mem_maximalIdeal_iff_residueCharacteristic_dvd (n : ℕ) :
    (n : F.valuationSubring) ∈ F.maximalIdeal ↔
      F.residueCharacteristic ∣ n := by
  rw [← F.toCompleteDVF.residue_eq_zero_iff (n : F.valuationSubring)]
  exact ringChar.spec F.residueField n

/-- Integer-valued maximal-ideal membership as a valuation inequality. -/
theorem valuationSubring_intCast_lt_one_iff_residueCharacteristic_dvd (z : ℤ) :
    F.toCompleteDVF.valuation ((z : F.valuationSubring) : K) < 1 ↔
      (F.residueCharacteristic : ℤ) ∣ z :=
  (F.toCompleteDVF.mem_maximalIdeal_iff
    (z : F.valuationSubring)).symm.trans
    (F.intCast_mem_maximalIdeal_iff_residueCharacteristic_dvd z)

/-- Natural-number-valued maximal-ideal membership as a valuation inequality. -/
theorem valuationSubring_natCast_lt_one_iff_residueCharacteristic_dvd (n : ℕ) :
    F.toCompleteDVF.valuation ((n : F.valuationSubring) : K) < 1 ↔
      F.residueCharacteristic ∣ n :=
  (F.toCompleteDVF.mem_maximalIdeal_iff
    (n : F.valuationSubring)).symm.trans
    (F.natCast_mem_maximalIdeal_iff_residueCharacteristic_dvd n)

/-- An integer prime to the residue characteristic has valuation one. -/
theorem valuationSubring_intCast_eq_one_of_not_residueCharacteristic_dvd {z : ℤ}
    (hz : ¬ (F.residueCharacteristic : ℤ) ∣ z) :
    F.toCompleteDVF.valuation ((z : F.valuationSubring) : K) = 1 := by
  have hle :=
    (F.toCompleteDVF.mem_valuationSubring_iff
      ((z : F.valuationSubring) : K)).1
      (z : F.valuationSubring).property
  exact le_antisymm hle (le_of_not_gt fun hlt ↦ hz ((valuationSubring_intCast_lt_one_iff_residueCharacteristic_dvd F z).mp hlt))

/-- A natural number prime to the residue characteristic has valuation one. -/
theorem valuationSubring_natCast_eq_one_of_not_residueCharacteristic_dvd {n : ℕ}
    (hn : ¬ F.residueCharacteristic ∣ n) :
    F.toCompleteDVF.valuation ((n : F.valuationSubring) : K) = 1 := by
  have hle :=
    (F.toCompleteDVF.mem_valuationSubring_iff
      ((n : F.valuationSubring) : K)).1
      (n : F.valuationSubring).property
  exact le_antisymm hle (le_of_not_gt fun hlt ↦ hn ((valuationSubring_natCast_lt_one_iff_residueCharacteristic_dvd F n).mp hlt))

/-- Field-level natural-number valuation criterion for the residue
characteristic. -/
theorem valuation_natCast_lt_one_iff_residueCharacteristic_dvd (n : ℕ) :
    F.toCompleteDVF.valuation (n : K) < 1 ↔
      F.residueCharacteristic ∣ n := by
  apply valuationSubring_natCast_lt_one_iff_residueCharacteristic_dvd

/-- Field-level integer valuation-one criterion away from the residue
characteristic. -/
theorem valuation_intCast_eq_one_of_not_residueCharacteristic_dvd {z : ℤ}
    (hz : ¬ (F.residueCharacteristic : ℤ) ∣ z) :
    F.toCompleteDVF.valuation (z : K) = 1 := by
  exact F.valuationSubring_intCast_eq_one_of_not_residueCharacteristic_dvd hz

/-- Field-level natural-number valuation-one criterion away from the residue
characteristic. -/
theorem valuation_natCast_eq_one_of_not_residueCharacteristic_dvd {n : ℕ}
    (hn : ¬ F.residueCharacteristic ∣ n) :
    F.toCompleteDVF.valuation (n : K) = 1 := by
  exact F.valuationSubring_natCast_eq_one_of_not_residueCharacteristic_dvd hn

end

/-- Every integer lies in the valuation subring.  This is the denominator
control input for the mixed-characteristic branch of the local-field structure classification. -/
theorem valuation_intCast_le_one (F : LocalField.{u, v} K) (z : ℤ) :
    F.toCompleteDVF.valuation (z : K) ≤ 1 := by
  exact
    (F.toCompleteDVF.mem_valuationSubring_iff
      ((z : F.valuationSubring) : K)).1 ((z : F.valuationSubring).property)

/-- Every natural number lies in the valuation subring. -/
theorem valuation_natCast_le_one (F : LocalField.{u, v} K) (n : ℕ) :
    F.toCompleteDVF.valuation (n : K) ≤ 1 := by
  simpa using F.valuation_intCast_le_one (n : ℤ)

/-- If the denominator of a rational number is prime to the residue
characteristic, then its valuation is the valuation of its numerator. -/
theorem valuation_ratCast_eq_intCast_of_not_residueCharacteristic_dvd_den
    (F : LocalField.{u, v} K) (q : ℚ)
    (hden : ¬ F.residueCharacteristic ∣ q.den) :
    F.toCompleteDVF.valuation (q : K) =
      F.toCompleteDVF.valuation (q.num : K) := by
  simpa [Rat.cast_def, F.valuation_natCast_eq_one_of_not_residueCharacteristic_dvd hden] using F.toCompleteDVF.valuation.map_div (q.num : K) (q.den : K)

/-- A rational number with denominator prime to the residue characteristic lies
in the valuation subring.  This is the local `ℤ_(p)` input for the converse
classification in the local-field structure theory, the local-field structure classification. -/
theorem valuation_ratCast_le_one_of_not_residueCharacteristic_dvd_den
    (F : LocalField.{u, v} K) (q : ℚ)
    (hden : ¬ F.residueCharacteristic ∣ q.den) :
    F.toCompleteDVF.valuation (q : K) ≤ 1 := by
  rw [F.valuation_ratCast_eq_intCast_of_not_residueCharacteristic_dvd_den q hden]
  apply F.valuation_intCast_le_one

/-- In a reduced rational number, if the denominator is divisible by the
residue characteristic then the numerator is not. -/
theorem not_residueCharacteristic_dvd_rat_num_of_dvd_den
    (F : LocalField.{u, v} K) (q : ℚ)
    (hden : F.residueCharacteristic ∣ q.den) :
    ¬ (F.residueCharacteristic : ℤ) ∣ q.num := by
  intro hnum
  exact F.residueCharacteristic_prime.ne_one (Nat.eq_one_of_dvd_coprimes q.reduced ((Int.natCast_dvd.mp hnum)) hden)

/-- For mixed-characteristic local fields, the rational numbers lying in the
valuation subring are exactly those whose denominator is prime to the residue
characteristic. -/
theorem valuation_ratCast_le_one_iff_not_residueCharacteristic_dvd_den
    (F : LocalField.{u, v} K) [CharZero K] (q : ℚ) :
    F.toCompleteDVF.valuation (q : K) ≤ 1 ↔
      ¬ F.residueCharacteristic ∣ q.den := by
  constructor
  · intro hle hden
    have hqVal :
        F.toCompleteDVF.valuation (q : K) =
          F.toCompleteDVF.valuation (q.num : K) /
            F.toCompleteDVF.valuation (q.den : K) := by
      calc
        _
            = F.toCompleteDVF.valuation ((q.num : K) / (q.den : K)) := by
              rw [Rat.cast_def]
        _ = F.toCompleteDVF.valuation (q.num : K) /
            F.toCompleteDVF.valuation (q.den : K) := F.toCompleteDVF.valuation.map_div (q.num : K) (q.den : K)
    refine (not_lt_of_ge hle) ?_
    rw [hqVal, (F.valuation_intCast_eq_one_of_not_residueCharacteristic_dvd (F.not_residueCharacteristic_dvd_rat_num_of_dvd_den q hden))]
    simpa using (one_lt_inv₀ (F.toCompleteDVF.valuation.pos_iff.2 (Nat.cast_ne_zero.mpr q.den_ne_zero))).2 ((F.valuation_natCast_lt_one_iff_residueCharacteristic_dvd q.den).2 hden)
  apply valuation_ratCast_le_one_of_not_residueCharacteristic_dvd_den

/-- The restriction of the local-field valuation to `ℚ` has the same valuation
subring as the `p`-adic valuation, where `p` is the residue characteristic. -/
theorem valuation_ratCast_le_one_iff_padicValuation_le_one
    (F : LocalField.{u, v} K) [CharZero K] (q : ℚ) :
    F.toCompleteDVF.valuation (q : K) ≤ 1 ↔
      Rat.padicValuation F.residueCharacteristic q ≤ 1 :=
  (F.valuation_ratCast_le_one_iff_not_residueCharacteristic_dvd_den q).trans
    (Rat.padicValuation_le_one_iff
      (p := F.residueCharacteristic) (x := q)).symm

variable (F : LocalField.{u, v} K) (p : ℕ) [CharP K p] (hp : p ≠ 0)

include hp in
/-- In positive equal characteristic, the residue field has the same
characteristic as the local field. -/
theorem residueField_charP_of_charP :
    CharP F.residueField p := CharP.of_ringHom_of_ne_zero F.residueMap p hp

include hp in
/-- In positive equal characteristic, the residue characteristic is the
characteristic of the local field. -/
theorem residueCharacteristic_eq_of_charP :
    F.residueCharacteristic = p := by
  have :=
    F.residueField_charP_of_charP p hp
  apply ringChar.eq

end LocalField
end LocalFieldTheory.DiscreteValuationField
