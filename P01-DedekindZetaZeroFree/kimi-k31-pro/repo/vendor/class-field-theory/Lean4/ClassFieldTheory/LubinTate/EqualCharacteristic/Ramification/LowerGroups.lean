module

public import ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.DisplacementValuation
public import ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups
public import ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumber
public import ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Lower ramification groups of equal-characteristic Lubin--Tate levels

This module identifies the actual lower ramification groups attached to the
chosen complete valuation, both by visible unit-parameter coefficients and by
their exact cardinalities.
-/

noncomputable section

open scoped LaurentSeries Pointwise PowerSeries

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LubinTate.EqualCharacteristic
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v y

variable {K : Type u} [Field K]

section ChosenRamificationTarget

variable {K₀ : Type} [Field K₀]



/-- Finite-dimensionality for the explicit level while computing its lower
ramification groups. -/
noncomputable local instance
    equalCharacteristicLubinTateLevelField_finiteDimensional_forLowerGroups
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_finiteDimensional F n

/-- Galoisness for the explicit level while computing its lower
ramification groups. -/
noncomputable local instance
    equalCharacteristicLubinTateLevelField_isGalois_forLowerGroups
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_isGalois F n





/-- The explicit finite unit-parameter bijection with the Galois group of the
chosen equal-characteristic Lubin--Tate level. -/
noncomputable def equalCharacteristicLubinTateUnitParameterEquivGal
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateUnitParameter F n ≃
      Gal((equalCharacteristicLubinTateLevelField F n) /
        LaurentSeries F.residueField) :=
  Equiv.ofBijective
    (equalCharacteristicLubinTateUnitParameterToGal F n)
    ⟨equalCharacteristicLubinTateUnitParameterToGal_injective F n,
      equalCharacteristicLubinTateUnitParameterToGal_surjective F n⟩

@[simp]
theorem equalCharacteristicLubinTateUnitParameterEquivGal_apply
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterEquivGal F n a =
      equalCharacteristicLubinTateUnitParameterToGal F n a :=
  rfl



 def equalCharacteristicLubinTateOneUnitParameter
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicLubinTateUnitParameter F n :=
  equalCharacteristicLubinTateUnitParameterOfCoefficients F n 1 (fun _ => 0)

@[simp]
private theorem equalCharacteristicLubinTateOneUnitParameterSeries
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicLubinTateUnitParameterSeries F n
        (equalCharacteristicLubinTateOneUnitParameter F n) = 1 := by
  ext i
  cases i with
  | zero =>
      simp [equalCharacteristicLubinTateOneUnitParameter,
        equalCharacteristicLubinTateUnitParameterOfCoefficients]
  | succ i =>
      by_cases hi : i < n
      · let j : Fin n := ⟨i, hi⟩
        simpa [j, equalCharacteristicLubinTateOneUnitParameter,
            equalCharacteristicLubinTateUnitParameterOfCoefficients] using
          equalCharacteristicLubinTateUnitParameterSeries_coeff_succ
            F n (equalCharacteristicLubinTateOneUnitParameter F n) j
      · simp [equalCharacteristicLubinTateUnitParameterSeries,
          equalCharacteristicLubinTateOneUnitParameter,
          equalCharacteristicLubinTateUnitParameterOfCoefficients]

@[simp]
private theorem equalCharacteristicLubinTateOneUnitParameterToGal
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateUnitParameterToGal F n
        (equalCharacteristicLubinTateOneUnitParameter F n) = 1 := by
  let a := equalCharacteristicLubinTateOneUnitParameter F n
  let sigma := equalCharacteristicLubinTateUnitParameterToGal F n a
  have ha :
      sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
    calc
      sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
          equalCharacteristicLubinTateUnitParameterLevelRoot F n a := by
            exact equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_gen F n a
      _ = equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen :=
        (equalCharacteristicLubinTateLevelBracket_gen F n a).symm
  by_contra hsigma
  have hne :=
    equalCharacteristicLubinTateUnitParameterSeries_sub_one_ne_zero_of_sigma_ne_one
      F n sigma a ha hsigma
  apply hne
  simp [a, equalCharacteristicLubinTateOneUnitParameterSeries]



@[simp]
private theorem equalCharacteristicLubinTateUnitParameterSeries_sub_one_eq_zero_iff
    (F : LocalField.{u, v} K)
    (n : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterSeries F n a - 1 = 0 ↔
      a = equalCharacteristicLubinTateOneUnitParameter F n := by
  constructor
  · intro ha
    have hseries :
        equalCharacteristicLubinTateUnitParameterSeries F n a = 1 :=
      sub_eq_zero.mp ha
    apply equalCharacteristicLubinTateUnitParameter_eq_of_coeff_eq F n
    intro i hi
    rw [hseries, equalCharacteristicLubinTateOneUnitParameterSeries]
  · rintro rfl
    rw [equalCharacteristicLubinTateOneUnitParameterSeries, sub_self]



 

 

 

 

 

 

 



 








end ChosenRamificationTarget

end LubinTate

end
