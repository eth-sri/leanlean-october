module

public import ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.GaloisAction
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
public import ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
public import ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness
public import ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/














set_option autoImplicit false

/-!
# The chosen complete valuation and primitive Lubin--Tate point

This module constructs the actual complete discrete valuation on an explicit
finite equal-characteristic Lubin--Tate level.  It proves that the chosen
primitive point generates the integral closure and is a uniformizer.
-/

noncomputable section

open scoped LaurentSeries Pointwise PowerSeries

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open LubinTate.EqualCharacteristic
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v y

variable {K : Type u} [Field K]















































































































section ChosenRamificationTarget

variable {K₀ : Type} [Field K₀]

/-- The canonical complete discrete valuation on the equal-characteristic
Laurent-series base used by the explicit Lubin--Tate level construction. -/
noncomputable def equalCharacteristicLubinTateBaseCompleteDVF
    (F : LocalField.{0, v} K₀) :
    ValuationTheory.DiscreteValuationField.CompleteDVF.{0, 0}
      F.residueField⸨X⸩ := by
  letI : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  letI : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  exact LocalFieldTheory.localCompleteDVF F.residueField⸨X⸩

/-- The valuation packaged by the chosen Laurent-series base is the canonical
valuation induced by the equal-characteristic valuative relation. -/
theorem equalCharacteristicLubinTateBaseCompleteDVF_valuation_eq
    (F : LocalField.{0, v} K₀) :
    (equalCharacteristicLubinTateBaseCompleteDVF F).valuation =
      letI : ValuativeRel F.residueField⸨X⸩ :=
        equalCharacteristicLaurentValuativeRel F
      ValuativeRel.valuation F.residueField⸨X⸩ := by
  let : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  change
    (LocalFieldTheory.localCompleteDVF F.residueField⸨X⸩).valuation =
      ValuativeRel.valuation F.residueField⸨X⸩
  unfold LocalFieldTheory.localCompleteDVF
  unfold ValuationTheory.Valuations.completeDVFOfCompleteValuedField
  rfl

/-- Identity on Laurent-series elements identifies the canonical valuative
integer ring with the valuation ring packaged by the chosen complete DVF. -/
 noncomputable def
    equalCharacteristicLaurentValuativeIntegerEquivLubinTateBaseValuationSubring
    (F : LocalField.{0, v} K₀) :
    letI : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    (ValuativeRel.valuation F.residueField⸨X⸩).integer ≃+*
      (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring := by
  letI : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  let hval :=
    equalCharacteristicLubinTateBaseCompleteDVF_valuation_eq F
  exact
    { toFun := fun x => ⟨x, by
        change
          (equalCharacteristicLubinTateBaseCompleteDVF F).valuation
              (x : F.residueField⸨X⸩) ≤ 1
        rw [hval]
        exact x.property⟩
      invFun := fun x => ⟨x, by
        change
          ValuativeRel.valuation F.residueField⸨X⸩
              (x : F.residueField⸨X⸩) ≤ 1
        rw [← hval]
        exact x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }

/-- Power series are exactly the valuation ring of the chosen
equal-characteristic Laurent-series base. -/
noncomputable def
    equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring
    (F : LocalField.{0, v} K₀) :
    F.residueField⟦X⟧ ≃+*
      (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring := by
  letI : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  exact
    (powerSeriesEquivLaurentValuativeInteger F.residueField).trans
      (equalCharacteristicLaurentValuativeIntegerEquivLubinTateBaseValuationSubring
        F)

/-- The power-series/valuation-ring equivalence is the usual inclusion after
coercion to the Laurent-series field. -/
@[simp]
theorem
    equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring_coe
    (F : LocalField.{0, v} K₀) (f : F.residueField⟦X⟧) :
    ((equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring F f :
        (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring) :
      F.residueField⸨X⸩) =
        (f : F.residueField⸨X⸩) := by
  rfl





























/-- The integral primitive division polynomial, with its coefficients
transported from `κ[[T]]` to the chosen base valuation ring. -/
noncomputable def
    equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring
    (F : LocalField.{0, v} K₀) (n : ℕ) :
    Polynomial
      (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring :=
  (equalCharacteristicLubinTateIntegralPrimitivePolynomial F n).map
    (equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring F)

/-- The primitive division polynomial remains monic after transport to the
chosen base valuation ring. -/
theorem
    equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring_monic
    (F : LocalField.{0, v} K₀) (n : ℕ) :
    (equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring
      F n).Monic :=
  (equalCharacteristicLubinTateIntegralPrimitivePolynomial_monic F n).map _

/-- Mapping the valuation-ring primitive polynomial into the Laurent-series
field recovers the original primitive division polynomial. -/
theorem
    equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring_map
    (F : LocalField.{0, v} K₀) (n : ℕ) :
    (equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring
        F n).map
          (algebraMap
            (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
            F.residueField⸨X⸩) =
      equalCharacteristicLubinTatePrimitivePolynomial F n := by
  rw [equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring,
    Polynomial.map_map,
    ← equalCharacteristicLubinTateIntegralPrimitivePolynomial_map]
  congr 1

 theorem equalCharacteristicLubinTateLevelCompleteDVFData_exists
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    ∃ target :
        ValuationTheory.DiscreteValuationField.CompleteDVF.{0, 0}
          (equalCharacteristicLubinTateLevelField F n),
      ∃ hExt :
          (equalCharacteristicLubinTateBaseCompleteDVF F).valuation.HasExtension
            target.valuation,
        letI :
            (equalCharacteristicLubinTateBaseCompleteDVF F).valuation.HasExtension
              target.valuation := hExt
        IsIntegralClosure target.valuationSubring
            (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
            (equalCharacteristicLubinTateLevelField F n) ∧
          ValuationTheory.DiscreteValuationField.ValuedExtension.degree
              (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
              target.toDVF =
            ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
                (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
                target.toDVF *
              ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
                (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
                target.toDVF := by
  let : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let : IsGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_isGalois F n
  exact
    ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_fundamental_identity
      (K := F.residueField⸨X⸩)
      (L := equalCharacteristicLubinTateLevelField F n)
      (equalCharacteristicLubinTateBaseCompleteDVF F)

/-- A complete-DVF structure on the explicit equal-characteristic
Lubin--Tate level field, chosen from its actual integral closure over
`κ((T))`. -/
noncomputable def equalCharacteristicLubinTateLevelCompleteDVF
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    ValuationTheory.DiscreteValuationField.CompleteDVF.{0, 0}
      (equalCharacteristicLubinTateLevelField F n) :=
  Classical.choose
    (equalCharacteristicLubinTateLevelCompleteDVFData_exists F n)

/-- The chosen level valuation extends the canonical Laurent-series base
valuation. -/
theorem equalCharacteristicLubinTateLevelCompleteDVF_hasExtension
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLubinTateBaseCompleteDVF F).valuation.HasExtension
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation :=
  Classical.choose
    (Classical.choose_spec
      (equalCharacteristicLubinTateLevelCompleteDVFData_exists F n))

/-- Provides the canonical extension instance for the chosen
equal-characteristic Lubin--Tate level valuation. -/
noncomputable instance
    equalCharacteristicLubinTateLevelCompleteDVF_hasExtensionInstance
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLubinTateBaseCompleteDVF F).valuation.HasExtension
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation :=
  equalCharacteristicLubinTateLevelCompleteDVF_hasExtension F n

/-- The valuation ring of the chosen level target is the actual integral
closure of the Laurent-series base valuation ring. -/
theorem equalCharacteristicLubinTateLevelCompleteDVF_isIntegralClosure
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsIntegralClosure
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
      (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
      (equalCharacteristicLubinTateLevelField F n) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (equalCharacteristicLubinTateLevelCompleteDVFData_exists F n))).1




















/-- The power-basis generator is integral over the chosen base valuation
ring.  Its witness is the transported integral primitive polynomial, not a
field-level integrality surrogate. -/
theorem
    equalCharacteristicLubinTateLevelPowerBasis_gen_isIntegral_over_baseValuationSubring
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsIntegral
      (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
      (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
  let P :=
    equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring F n
  refine
    ⟨P,
      equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring_monic
        F n, ?_⟩
  calc
    Polynomial.aeval
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen P =
        Polynomial.aeval
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen
          (P.map
            (algebraMap
              (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
              F.residueField⸨X⸩)) := by
            symm
            exact Polynomial.aeval_map_algebraMap
              F.residueField⸨X⸩
              (equalCharacteristicLubinTateLevelPowerBasis F n).gen P
    _ = Polynomial.aeval
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen
        (equalCharacteristicLubinTatePrimitivePolynomial F n) := by
          rw [
            equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring_map]
    _ = Polynomial.aeval
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen
        (minpoly F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen) := by
          rw [equalCharacteristicLubinTateLevelPowerBasis_minpoly]
    _ = 0 :=
      minpoly.aeval F.residueField⸨X⸩
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen

/-- The chosen primitive Lubin--Tate division point belongs to the actual
integral-closure valuation ring selected on the level field. -/
theorem
    equalCharacteristicLubinTateLevelPowerBasis_gen_mem_valuationSubring
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLubinTateLevelPowerBasis F n).gen ∈
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation.valuationSubring := by
  let :
      IsIntegralClosure
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
        (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
        (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelCompleteDVF_isIntegralClosure F n
  rcases
      (IsIntegralClosure.isIntegral_iff
        (A :=
          (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring)
        (R :=
          (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring)
        (B := equalCharacteristicLubinTateLevelField F n)).1
        (equalCharacteristicLubinTateLevelPowerBasis_gen_isIntegral_over_baseValuationSubring
          F n) with
    ⟨x, hx⟩
  change
    (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen ≤ 1
  rw [← hx]
  exact x.property

/-- The primitive level-`n+1` division point as an element of the chosen
target valuation ring.  Its norm computation below proves that this element
is a uniformizer. -/
noncomputable def equalCharacteristicLubinTatePrimitivePointInteger
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring :=
  ⟨(equalCharacteristicLubinTateLevelPowerBasis F n).gen,
    equalCharacteristicLubinTateLevelPowerBasis_gen_mem_valuationSubring F n⟩

/-- The valuation-ring primitive point has the original power-basis generator
as its underlying level-field element. -/
@[simp]
theorem equalCharacteristicLubinTatePrimitivePointInteger_coe
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLubinTatePrimitivePointInteger F n).val =
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen :=
  rfl









































































































































































section PrimitivePointUniformizer




















































































































































































































































end PrimitivePointUniformizer
























































































section PrimitivePointDisplacementValuation

noncomputable local instance
    equalCharacteristicLubinTateLevelField_finiteDimensional_forDisplacementValuation
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_finiteDimensional F n

noncomputable local instance
    equalCharacteristicLubinTateLevelField_isGalois_forDisplacementValuation
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_isGalois F n









































end PrimitivePointDisplacementValuation

end ChosenRamificationTarget

end LubinTate

end
