module

public import ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.PrimitivePoint
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PolynomialRootProximity
public import ValuedFieldTheory.Ramification.HilbertRamification.ValuationKrasner

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Valuation of primitive-point displacement

This module computes the normalized additive valuation of the displacement of
the chosen primitive Lubin--Tate point from the first visible coefficient of
the corresponding unit parameter.
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

section PrimitivePointDisplacementValuation

attribute [local instance]
  equalCharacteristicLubinTateLevelField_finiteDimensional_forDisplacementValuation
  equalCharacteristicLubinTateLevelField_isGalois_forDisplacementValuation

 noncomputable def equalCharacteristicLubinTateCoefficientInteger
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (c : F.residueField) :
    (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring :=
  integerMap
    (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
    (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF
    (equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring F
      (PowerSeries.C c))

@[simp]
private theorem equalCharacteristicLubinTateCoefficientInteger_zero
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateCoefficientInteger F n 0 = 0 := by
  simp [equalCharacteristicLubinTateCoefficientInteger]

@[simp]
private theorem equalCharacteristicLubinTateCoefficientInteger_coe
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (c : F.residueField) :
    (equalCharacteristicLubinTateCoefficientInteger F n c).val =
        algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (algebraMap F.residueField F.residueField⸨X⸩ c) := by
  rfl

 noncomputable def equalCharacteristicLubinTatePiEndInteger
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ)
    (x :
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring) :
    (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring :=
  x ^ Nat.card F.residueField +
    integerMap
        (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
        (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF
        (equalCharacteristicLubinTateBaseUniformizerInteger F) * x

@[simp]
private theorem equalCharacteristicLubinTatePiEndInteger_coe
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ)
    (x :
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring) :
    (equalCharacteristicLubinTatePiEndInteger F n x).val =
      equalCharacteristicLubinTateAmbientPiEnd F
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (equalCharacteristicLaurentUniformizer F))
        x.val := by
  simp [equalCharacteristicLubinTatePiEndInteger,
    equalCharacteristicLubinTateAmbientPiEnd_apply,
    integerMap_apply,
    equalCharacteristicLubinTateBaseUniformizerInteger_coe]

 noncomputable def equalCharacteristicLubinTatePiIterateInteger
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    ℕ →
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
  | 0 => equalCharacteristicLubinTatePrimitivePointInteger F n
  | i + 1 =>
      equalCharacteristicLubinTatePiEndInteger F n
        (equalCharacteristicLubinTatePiIterateInteger F n i)

private theorem equalCharacteristicLubinTateAmbientPiIterate_succ_left
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n i : ℕ) (x : equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicLubinTateAmbientPiIterate F
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (equalCharacteristicLaurentUniformizer F))
        (i + 1) x =
      equalCharacteristicLubinTateAmbientPiEnd F
          (algebraMap F.residueField⸨X⸩
            (equalCharacteristicLubinTateLevelField F n)
            (equalCharacteristicLaurentUniformizer F))
        (equalCharacteristicLubinTateAmbientPiIterate F
          (algebraMap F.residueField⸨X⸩
            (equalCharacteristicLubinTateLevelField F n)
            (equalCharacteristicLaurentUniformizer F))
          i x) := by
  change
    ((equalCharacteristicLubinTateAmbientPiEnd F
      (algebraMap F.residueField⸨X⸩
        (equalCharacteristicLubinTateLevelField F n)
        (equalCharacteristicLaurentUniformizer F))) ^ (i + 1)) x =
      equalCharacteristicLubinTateAmbientPiEnd F
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (equalCharacteristicLaurentUniformizer F))
        (((equalCharacteristicLubinTateAmbientPiEnd F
          (algebraMap F.residueField⸨X⸩
            (equalCharacteristicLubinTateLevelField F n)
            (equalCharacteristicLaurentUniformizer F))) ^ i) x)
  rw [pow_succ']
  rfl

@[simp]
private theorem equalCharacteristicLubinTatePiIterateInteger_coe
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n i : ℕ) :
    (equalCharacteristicLubinTatePiIterateInteger F n i).val =
      equalCharacteristicLubinTateAmbientPiIterate F
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (equalCharacteristicLaurentUniformizer F))
        i (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
  induction i with
  | zero =>
      simp [equalCharacteristicLubinTatePiIterateInteger]
  | succ i ih =>
      rw [equalCharacteristicLubinTatePiIterateInteger,
        equalCharacteristicLubinTatePiEndInteger_coe, ih,
        equalCharacteristicLubinTateAmbientPiIterate_succ_left]







 noncomputable def equalCharacteristicLubinTateBracketInteger
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (u : F.residueField⟦X⟧) :
    (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring :=
  ∑ i ∈ Finset.range (n + 1),
    equalCharacteristicLubinTateCoefficientInteger F n
        (PowerSeries.coeff i u) *
      equalCharacteristicLubinTatePiIterateInteger F n i

@[simp]
private theorem equalCharacteristicLubinTateBracketInteger_coe
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (u : F.residueField⟦X⟧) :
    (equalCharacteristicLubinTateBracketInteger F n u).val =
      equalCharacteristicLubinTateAmbientBracket F
        ((algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)).comp
            (algebraMap F.residueField F.residueField⸨X⸩))
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (equalCharacteristicLaurentUniformizer F))
        (n + 1) u (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
  rw [equalCharacteristicLubinTateBracketInteger,
    equalCharacteristicLubinTateAmbientBracket_apply]
  let j :
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation.valuationSubring →+*
        equalCharacteristicLubinTateLevelField F n :=
    (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation.valuationSubring.subtype
  let term : ℕ →
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation.valuationSubring :=
    fun i => equalCharacteristicLubinTateCoefficientInteger F n (PowerSeries.coeff i u) *
      equalCharacteristicLubinTatePiIterateInteger F n i
  change
    j (∑ i ∈ Finset.range (n + 1), term i) =
      _
  have hsum (s : Finset ℕ) :
      j (∑ i ∈ s, term i) = ∑ i ∈ s, j (term i) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, j.map_zero]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [RingHom.map_add j (term i) (∑ k ∈ s, term k), ih]
  rw [hsum (Finset.range (n + 1))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [j.map_mul]
  change
    (equalCharacteristicLubinTateCoefficientInteger F n
        (PowerSeries.coeff i u)).val *
        (equalCharacteristicLubinTatePiIterateInteger F n i).val =
      _
  rw [equalCharacteristicLubinTateCoefficientInteger_coe,
    equalCharacteristicLubinTatePiIterateInteger_coe]
  rfl













/-- A nonidentity automorphism has a genuinely nonzero visible coefficient
difference from the identity parameter. -/
theorem
    equalCharacteristicLubinTateUnitParameterSeries_sub_one_ne_zero_of_sigma_ne_one
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ)
    (sigma : Gal((equalCharacteristicLubinTateLevelField F n) /
      F.residueField⸨X⸩))
    (a : equalCharacteristicLubinTateUnitParameter F n)
    (ha :
      sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen)
    (hsigma : sigma ≠ 1) :
    equalCharacteristicLubinTateUnitParameterSeries F n a - 1 ≠ 0 := by
  intro hu
  apply hsigma
  have hseries :
      equalCharacteristicLubinTateUnitParameterSeries F n a = 1 :=
    sub_eq_zero.mp hu
  have hone :
      equalCharacteristicLubinTateLevelBracket F n (n + 1) 1
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
    apply Subtype.ext
    change
      equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1) 1
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
        chosenEqualCharacteristicLubinTatePrimitiveRoot F n
    exact
      equalCharacteristicLubinTateAmbientBracket_one_apply_of_torsion F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n)
  apply AlgEquiv.coe_toAlgHom_injective
  apply (equalCharacteristicLubinTateLevelPowerBasis F n).algHom_ext
  change
    sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      (equalCharacteristicLubinTateLevelPowerBasis F n).gen
  calc
    sigma (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen := ha
    _ = equalCharacteristicLubinTateLevelBracket F n (n + 1) 1
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
            rw [hseries]
    _ = (equalCharacteristicLubinTateLevelPowerBasis F n).gen := hone



end PrimitivePointDisplacementValuation


end ChosenRamificationTarget

end LubinTate

end
