module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CompletedUnramifiedField
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveIrreducible
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveTorsion
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.SplittingField.Construction

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The completed theta-intertwining theorem: a completed Lubin--Tate level field

Let `k` be the residue field and put `K∞ = (AlgebraicClosure k)((T))`.
This file base-changes the primitive Lubin--Tate polynomial to `K∞`, takes
its genuine splitting field, and equips that finite extension with the
spectral norm.  A chosen primitive root is proved to lie in the maximal ideal
of the resulting complete valued field, hence is an actual analytic
evaluation point for the theta series of the completed theta-intertwining theorem.
-/

noncomputable section

open Filter
open scoped LaurentSeries NNReal Polynomial PowerSeries Topology WithZero

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The coefficientwise algebra structure
`k((T)) → (AlgebraicClosure k)((T))`. -/
noncomputable local instance equalCharacteristicCompletedLevelBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

 instance equalCharacteristicCompletedLevelBaseCharP
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] :
    CharP (equalCharacteristicCompletedUnramifiedField F.residueField)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap F.residueField
      (equalCharacteristicCompletedUnramifiedField F.residueField)).injective
    F.residueCharacteristic

/-- The primitive level-`n+1` polynomial after coefficientwise base change
to `(AlgebraicClosure k)((T))`. -/
def equalCharacteristicCompletedPrimitivePolynomial
    (F : LocalField.{u, v} K) (n : ℕ) :
    Polynomial (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  (equalCharacteristicLubinTatePrimitivePolynomial F n).map
    (algebraMap F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField))

/-- The completed primitive polynomial is monic. -/
theorem equalCharacteristicCompletedPrimitivePolynomial_monic
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedPrimitivePolynomial F n).Monic :=
  (equalCharacteristicLubinTatePrimitivePolynomial_monic F n).map _

/-- The completed primitive polynomial has degree `(q - 1) * q ^ n`. -/
theorem equalCharacteristicCompletedPrimitivePolynomial_natDegree
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedPrimitivePolynomial F n).natDegree =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  rw [equalCharacteristicCompletedPrimitivePolynomial,
    (equalCharacteristicLubinTatePrimitivePolynomial_monic F n).natDegree_map,
    equalCharacteristicLubinTatePrimitivePolynomial_natDegree]

/-- The actual finite completed level field used to evaluate theta. -/
def equalCharacteristicCompletedLevelField
    (F : LocalField.{u, v} K) (n : ℕ) :=
  (equalCharacteristicCompletedPrimitivePolynomial F n).SplittingField

/-- The splitting field of the completed primitive polynomial is a field. -/
instance equalCharacteristicCompletedLevelField_field
    (F : LocalField.{u, v} K) (n : ℕ) :
    Field (equalCharacteristicCompletedLevelField F n) := by
  change Field (equalCharacteristicCompletedPrimitivePolynomial F n).SplittingField
  infer_instance

/-- The completed level field is an algebra over the completed unramified field. -/
instance equalCharacteristicCompletedLevelField_algebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) := by
  change Algebra (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedPrimitivePolynomial F n).SplittingField
  infer_instance

noncomputable local instance equalCharacteristicCompletedLevelLaurentAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  ((algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)).comp
    (algebraMap F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField))).toAlgebra

noncomputable local instance equalCharacteristicCompletedLevelScalarTower
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

 instance equalCharacteristicCompletedLevelCharP
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) :
    CharP (equalCharacteristicCompletedLevelField F n)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)).injective
    F.residueCharacteristic

section

local instance equalCharacteristicCompletedLevelField_module
    (F : LocalField.{u, v} K) (n : ℕ) :
    @Module (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)
      (inferInstance : DivisionRing
        (equalCharacteristicCompletedUnramifiedField F.residueField)).toRing.toSemiring
      (inferInstance : AddCommGroup
        (equalCharacteristicCompletedLevelField F n)).toAddCommMonoid :=
  @Algebra.toModule
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedLevelField F n) _ _
    (equalCharacteristicCompletedLevelField_algebra F n)

/-- The completed level field is finite-dimensional over its completed base. -/
instance equalCharacteristicCompletedLevelField_finiteDimensionalInstance
    (F : LocalField.{u, v} K) (n : ℕ) :
    FiniteDimensional
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) := by
  change FiniteDimensional
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedPrimitivePolynomial F n).SplittingField
  infer_instance

/-- The completed level field is algebraic over its completed base. -/
instance equalCharacteristicCompletedLevelField_isAlgebraic
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra.IsAlgebraic
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  @Algebra.IsAlgebraic.of_finite
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedLevelField F n) _ _ _
    (equalCharacteristicCompletedLevelField_algebra F n)
    (equalCharacteristicCompletedLevelField_finiteDimensionalInstance F n)

/-- Comparison with the library splitting-field model. -/
def equalCharacteristicCompletedLevelFieldEquivSplittingField
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicCompletedLevelField F n ≃ₐ[
      equalCharacteristicCompletedUnramifiedField F.residueField]
      (equalCharacteristicCompletedPrimitivePolynomial F n).SplittingField :=
  AlgEquiv.refl

/-- Construct a named completed-level element from the splitting-field
model. -/
def equalCharacteristicCompletedLevelFieldOfSplittingField
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedPrimitivePolynomial F n).SplittingField →ₐ[
      equalCharacteristicCompletedUnramifiedField F.residueField]
      equalCharacteristicCompletedLevelField F n :=
  (equalCharacteristicCompletedLevelFieldEquivSplittingField F n).symm.toAlgHom

/-- The defining primitive polynomial splits over the named completed level
field. -/
theorem equalCharacteristicCompletedPrimitivePolynomial_splits
    (F : LocalField.{u, v} K) (n : ℕ) :
    ((equalCharacteristicCompletedPrimitivePolynomial F n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n))).Splits := 
  Polynomial.SplittingField.splits
    (equalCharacteristicCompletedPrimitivePolynomial F n)

/-- The roots of the defining polynomial generate the named completed level
field. -/
theorem equalCharacteristicCompletedPrimitivePolynomial_adjoin_rootSet
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ((equalCharacteristicCompletedPrimitivePolynomial F n).rootSet
          (equalCharacteristicCompletedLevelField F n) :
          Set (equalCharacteristicCompletedLevelField F n)) = ⊤ := 
  Polynomial.SplittingField.adjoin_rootSet
    (equalCharacteristicCompletedPrimitivePolynomial F n)

 theorem equalCharacteristicCompletedPrimitivePolynomial_map_degree_ne_zero
    (F : LocalField.{u, v} K) (n : ℕ) :
    ((equalCharacteristicCompletedPrimitivePolynomial F n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n))).degree ≠ 0 := by
  have hmonic := (equalCharacteristicCompletedPrimitivePolynomial_monic F n).map
    (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n))
  rw [Polynomial.degree_eq_natDegree hmonic.ne_zero,
    (equalCharacteristicCompletedPrimitivePolynomial_monic F n).natDegree_map,
    equalCharacteristicCompletedPrimitivePolynomial_natDegree]
  exact_mod_cast (Nat.mul_pos
    (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
    (Nat.pow_pos Nat.card_pos)).ne'

/-- A chosen primitive root in the completed level field. -/
def equalCharacteristicCompletedPrimitiveRoot
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicCompletedLevelField F n :=
  equalCharacteristicCompletedLevelFieldOfSplittingField F n
    (Polynomial.rootOfSplits
      (Polynomial.SplittingField.splits
        (equalCharacteristicCompletedPrimitivePolynomial F n))
      (equalCharacteristicCompletedPrimitivePolynomial_map_degree_ne_zero F n))

/-- The chosen element is a root of the base-changed primitive polynomial.
-/
theorem equalCharacteristicCompletedPrimitiveRoot_isRoot
    (F : LocalField.{u, v} K) (n : ℕ) :
    ((equalCharacteristicCompletedPrimitivePolynomial F n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n))).IsRoot
          (equalCharacteristicCompletedPrimitiveRoot F n) := 
  Polynomial.eval_rootOfSplits
    (Polynomial.SplittingField.splits
      (equalCharacteristicCompletedPrimitivePolynomial F n))
    (equalCharacteristicCompletedPrimitivePolynomial_map_degree_ne_zero F n)

/-- The Laurent parameter in the completed maximal-unramified base. -/
def equalCharacteristicCompletedBaseUniformizer
    (F : LocalField.{u, v} K) :
    equalCharacteristicCompletedUnramifiedField F.residueField :=
  equalCharacteristicCompletedUnramifiedFieldSingle F.residueField 1 1

/-- Coefficientwise base change fixes the Laurent parameter. -/
theorem equalCharacteristicCompletedBase_algebraMap_uniformizer
    (F : LocalField.{u, v} K) :
    algebraMap F.residueField⸨X⸩
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicLaurentUniformizer F) =
      equalCharacteristicCompletedBaseUniformizer F := by
  apply
    (equalCharacteristicCompletedUnramifiedFieldEquivLaurentSeries
      F.residueField).injective
  change
    laurentSeriesCoefficientMap
        (algebraMap F.residueField (AlgebraicClosure F.residueField))
        (equalCharacteristicLaurentUniformizer F) =
      HahnSeries.single 1 1
  ext m
  cases m with
  | ofNat i =>
      by_cases hi : i = 1
      · subst i
        simp [equalCharacteristicLaurentUniformizer,
          laurentSeriesCoefficientMap]
      · simp [equalCharacteristicLaurentUniformizer,
          laurentSeriesCoefficientMap, HahnSeries.coeff_single_of_ne, hi]
  | negSucc i =>
    simp [equalCharacteristicLaurentUniformizer,
      laurentSeriesCoefficientMap]

/-- The image of `T` in the completed level field. -/
def equalCharacteristicCompletedLevelUniformizer
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicCompletedLevelField F n :=
  algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedLevelField F n)
    (equalCharacteristicCompletedBaseUniformizer F)

/-- The chosen root satisfies the genuine primitive Lubin--Tate equation
over the completed-unramified base. -/
theorem equalCharacteristicCompletedPrimitiveRoot_equation
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicCompletedLevelUniformizer F n) n
        (equalCharacteristicCompletedPrimitiveRoot F n) ^
          (Nat.card F.residueField - 1) +
      equalCharacteristicCompletedLevelUniformizer F n = 0 := by
  have hroot := equalCharacteristicCompletedPrimitiveRoot_isRoot F n
  change Polynomial.eval
      (equalCharacteristicCompletedPrimitiveRoot F n)
      (((equalCharacteristicLubinTatePrimitivePolynomial F n).map
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicCompletedUnramifiedField F.residueField))).map
        (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
          (equalCharacteristicCompletedLevelField F n))) = 0 at hroot
  rw [Polynomial.map_map, Polynomial.eval_map,
    equalCharacteristicLubinTatePrimitivePolynomial_eval₂] at hroot
  have ht :
      ((algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)).comp
          (algebraMap F.residueField⸨X⸩
            (equalCharacteristicCompletedUnramifiedField F.residueField)))
        (equalCharacteristicLaurentUniformizer F) =
      equalCharacteristicCompletedLevelUniformizer F n := by
    rw [RingHom.comp_apply,
      equalCharacteristicCompletedBase_algebraMap_uniformizer]
    rfl
  rwa [ht] at hroot
