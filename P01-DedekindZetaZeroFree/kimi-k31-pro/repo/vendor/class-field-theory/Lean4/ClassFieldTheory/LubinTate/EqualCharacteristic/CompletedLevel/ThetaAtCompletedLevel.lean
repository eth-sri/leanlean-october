module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaFirstIdentity
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaEvaluation

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# The completed theta-intertwining theorem: theta at a completed Lubin--Tate level

This file evaluates the theta series analytically at the chosen primitive
division point in the completed level field.
-/

noncomputable section

open Filter
open scoped LaurentSeries NNReal PowerSeries PowerSeries.WithPiTopology
  Topology Valued WithZero


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

noncomputable local instance equalCharacteristicThetaAtLevelBaseValuationIsNontrivial
    (F : LocalField.{u, v} K) :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰).IsNontrivial :=
  equalCharacteristicCompletedBaseValuationIsNontrivial F.residueField

noncomputable local instance equalCharacteristicThetaAtLevelBaseValuationRankOne
    (F : LocalField.{u, v} K) :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰).RankOne :=
  equalCharacteristicCompletedBaseValuationRankOne F.residueField

noncomputable local instance equalCharacteristicThetaAtLevelBaseNormedField
    (F : LocalField.{u, v} K) :
    NontriviallyNormedField
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedBaseNormedField F.residueField

noncomputable local instance equalCharacteristicThetaAtLevelNormedField
    (F : LocalField.{u, v} K) (n : ℕ) :
    NontriviallyNormedField (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelNormedField F n

noncomputable local instance equalCharacteristicThetaAtLevelIsUltrametric
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUltrametricDist (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelIsUltrametric F n

noncomputable local instance equalCharacteristicThetaAtLevelCompleteSpace
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelCompleteSpace F n

noncomputable local instance equalCharacteristicThetaAtLevelValued
    (F : LocalField.{u, v} K) (n : ℕ) :
    Valued (equalCharacteristicCompletedLevelField F n) ℝ≥0 :=
  equalCharacteristicCompletedLevelValued F n

noncomputable local instance equalCharacteristicThetaAtLevelLinearTopology
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsLinearTopology
      (Valued.integer (equalCharacteristicCompletedLevelField F n))
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerLinearTopology

noncomputable local instance equalCharacteristicThetaAtLevelCompleteInteger
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerCompleteSpace

noncomputable local instance equalCharacteristicThetaAtLevelUniformAddGroup
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUniformAddGroup
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerIsUniformAddGroup

/-- The integral inclusion from the completed maximal-unramified base into
the completed level field.  Integrality is preserved because the spectral
norm extends the base norm. -/
noncomputable def equalCharacteristicCompletedBaseIntegerToLevel
    (F : LocalField.{u, v} K) (n : ℕ) :
    Valued.integer
        (equalCharacteristicCompletedUnramifiedField F.residueField) →+*
      Valued.integer (equalCharacteristicCompletedLevelField F n) where
  toFun x := ⟨algebraMap
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) x, by
    change ‖algebraMap
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) (x :
        equalCharacteristicCompletedUnramifiedField F.residueField)‖₊ ≤ 1
    exact_mod_cast (show ‖algebraMap
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) (x :
        equalCharacteristicCompletedUnramifiedField F.residueField)‖ ≤ 1 by
          change spectralNorm
            (equalCharacteristicCompletedUnramifiedField F.residueField)
            (equalCharacteristicCompletedLevelField F n)
            (algebraMap
              (equalCharacteristicCompletedUnramifiedField F.residueField)
              (equalCharacteristicCompletedLevelField F n) (x :
                equalCharacteristicCompletedUnramifiedField
                  F.residueField)) ≤ 1
          rw [spectralNorm_extends,
            Valued.toNormedField.norm_le_one_iff]
          exact x.property)⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- Coefficients in `(AlgebraicClosure k)[[T]]`, analytically included in
the valuation ring of the completed level field. -/
noncomputable def equalCharacteristicCompletedLevelCoefficientHom
    (F : LocalField.{u, v} K) (n : ℕ) :
    (AlgebraicClosure F.residueField)⟦X⟧ →+*
      Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  (equalCharacteristicCompletedBaseIntegerToLevel F n).comp
    (powerSeriesEquivLaurentInteger
      (AlgebraicClosure F.residueField)).toRingHom

 noncomputable local instance equalCharacteristicThetaCoefficientUniformSpace
    (F : LocalField.{u, v} K) :
    UniformSpace ((AlgebraicClosure F.residueField)⟦X⟧) := ⊥

 theorem equalCharacteristicCompletedLevelCoefficientHom_continuous
    (F : LocalField.{u, v} K) (n : ℕ) :
    Continuous (equalCharacteristicCompletedLevelCoefficientHom F n) :=
  continuous_of_discreteTopology

 noncomputable local instance equalCharacteristicThetaAtLevelCoefficientAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra ((AlgebraicClosure F.residueField)⟦X⟧)
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  (equalCharacteristicCompletedLevelCoefficientHom F n).toAlgebra

/-- Analytic evaluation of an outer power series at an integral,
topologically nilpotent point of the completed level field. -/
noncomputable def equalCharacteristicCompletedLevelEvaluation
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (ha : PowerSeries.HasEval a) :
    ((AlgebraicClosure F.residueField)⟦X⟧)⟦X⟧ →+*
      Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  PowerSeries.eval₂Hom
    (equalCharacteristicCompletedLevelCoefficientHom_continuous F n) ha

/-- States the theorem `equalCharacteristicCompletedLevelEvaluation_X`. -/
@[simp]
theorem equalCharacteristicCompletedLevelEvaluation_X
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (ha : PowerSeries.HasEval a) :
    equalCharacteristicCompletedLevelEvaluation F n a ha PowerSeries.X = a := by
  rw [equalCharacteristicCompletedLevelEvaluation,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]

/-- States the theorem `equalCharacteristicCompletedLevelEvaluation_C`. -/
@[simp]
theorem equalCharacteristicCompletedLevelEvaluation_C
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (ha : PowerSeries.HasEval a)
    (f : (AlgebraicClosure F.residueField)⟦X⟧) :
    equalCharacteristicCompletedLevelEvaluation F n a ha (PowerSeries.C f) =
      equalCharacteristicCompletedLevelCoefficientHom F n f := by
  rw [equalCharacteristicCompletedLevelEvaluation,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]

/-- The image of `T` in the valuation ring of the completed level field. -/
noncomputable def equalCharacteristicCompletedLevelUniformizerInteger
    (F : LocalField.{u, v} K) (n : ℕ) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelCoefficientHom F n PowerSeries.X

























end EqualCharacteristic
end LubinTate

end
