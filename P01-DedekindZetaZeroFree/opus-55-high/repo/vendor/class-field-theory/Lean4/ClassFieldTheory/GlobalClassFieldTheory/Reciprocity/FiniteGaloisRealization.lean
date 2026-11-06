module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationFinitePlace
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationNormQuotient
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.NormTopology

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Reciprocity for a realized finite Galois number-field tower

This module equips the compatible fixed-field realization of `L / K` with the
finite-dimensional and number-field instances needed by global class formation,
then transports abstract reciprocity back to the original tower.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

/-- Fix the canonical class-group structure before forming norm quotients. -/
@[instance_reducible]
 def realizedTowerIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] realizedTowerIdeleClassCommGroup

 theorem realizedTowerIdeleClassIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) := by apply normIdeleClassGroup_isMulCommutative <;> assumption

attribute [local instance] realizedTowerIdeleClassIsMulCommutative

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem numberFieldTowerAbstractBaseFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)

theorem numberFieldTowerAbstractRelativeFiniteDimensional :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (numberFieldTowerTopSubgroup L)
    (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
    (numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)
    (numberFieldTowerExtensionQuotientFinite K L)

omit [FiniteDimensional K L] [IsGalois K L] in
theorem numberFieldTowerAbstractScalarTower :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem numberFieldTowerAbstractTopFiniteDimensional :
    FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) := by
  let := numberFieldTowerAbstractBaseFiniteDimensional K L
  let := numberFieldTowerAbstractRelativeFiniteDimensional K L
  let := numberFieldTowerAbstractScalarTower K L
  exact FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ)
      (numberFieldTowerBaseSubgroup K L))
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L))

omit [FiniteDimensional K L] [IsGalois K L] in
 theorem numberFieldTowerAbstractBaseNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) := by apply GlobalClassFieldTheory.Reciprocity.towerNormAbstractBaseNumberField <;> assumption

 theorem numberFieldTowerAbstractTopNumberField :
    NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) := by
  let := numberFieldTowerAbstractTopFiniteDimensional K L
  exact NumberField.of_module_finite ℚ _

@[reducible]  def numberFieldTowerRestrictedTopAlgebra :
    Algebra
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L))
      ((abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).restrictScalars ℚ) :=
  (IntermediateField.inclusion
    (abstractFixedField_le ℚ (SeparableClosure ℚ)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L))).toRingHom.toAlgebra

theorem ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_symm_mk
    {K₀ L₀ K₁ L₁ : Type}
    [Field K₀] [NumberField K₀]
    [Field L₀] [NumberField L₀] [Algebra K₀ L₀]
    [Field K₁] [NumberField K₁]
    [Field L₁] [NumberField L₁] [Algebra K₁ L₁]
    (eK : K₀ ≃ₐ[ℚ] K₁)
    (eL : L₀ ≃ₐ[ℚ] L₁)
    (h : ∀ x : K₀,
      eL (algebraMap K₀ L₀ x) =
        algebraMap K₁ L₁ (eK x))
    (c : IdeleClassGroup K₁) :
    (ordinaryIdeleClassNormQuotientCongrOfAlgEquiv eK eL h).symm
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K₁ L₁).range c) =
      QuotientGroup.mk'
        (_root_.ideleClassNorm K₀ L₀).range
        ((ideleClassCongr eK).symm c) := by
  rfl

 def numberFieldTowerFiniteNormClassPublicValue
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient K L
    (finiteNormClass rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L) a)

 def numberFieldTowerFiniteNormClassExpectedValue
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  Additive.ofMul
    (QuotientGroup.mk'
      (_root_.ideleClassNorm K L).range
      (Additive.toMul
        ((numberFieldTowerIdeleClassEquivAmbientFixed K L).symm a)))

 def numberFieldTowerFiniteNormClassDirectComparisonValue
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) := by
  let H := numberFieldTowerBaseSubgroup K L
  let J := numberFieldTowerTopSubgroup L
  let hJH : J.toSubgroup ≤ H.toSubgroup :=
    numberFieldTowerTopSubgroup_le_baseSubgroup K L
  let hnormal := numberFieldTowerExtensionSubgroupNormal K L
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hJH
  letI : NumberField F := numberFieldTowerAbstractBaseNumberField K L
  letI : NumberField E := numberFieldTowerAbstractTopNumberField K L
  let eBase : K ≃ₐ[ℚ] F := numberFieldTowerAbstractBaseFieldEquiv K L
  let eTop : L ≃ₐ[ℚ] E := numberFieldTowerAbstractTopFieldEquiv K L
  have hcompat : ∀ x : K,
      eTop (algebraMap K L x) = algebraMap F E (eBase x) :=
    numberFieldTowerAbstractFieldEquiv_algebraMap K L
  let actualFieldEquiv :
      (IdeleClassGroup K ⧸ (_root_.ideleClassNorm K L).range) ≃*
        (IdeleClassGroup F ⧸ (_root_.ideleClassNorm F E).range) :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (K := K) (L := L) (K' := F) (L' := E) eBase eTop hcompat
  exact
    MulEquiv.toAdditive
      actualFieldEquiv.symm
      (rationalFiniteNormQuotientEquivIdeleClassNormQuotient
        (hKfinite := numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)
        (hfinite := numberFieldTowerExtensionQuotientFinite K L)
        H J hJH hnormal
        (finiteNormClass rationalIdeleClassRepresentation H J hJH a))

theorem numberFieldTowerFiniteNormClassPublicValue_eq_directComparison
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)) :
    numberFieldTowerFiniteNormClassPublicValue K L a =
      numberFieldTowerFiniteNormClassDirectComparisonValue K L a := by
  rfl

 def numberFieldTowerActualNormClassRepresentativeValue
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) := by
  let H := numberFieldTowerBaseSubgroup K L
  let J := numberFieldTowerTopSubgroup L
  let hJH : J.toSubgroup ≤ H.toSubgroup :=
    numberFieldTowerTopSubgroup_le_baseSubgroup K L
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hJH
  letI : NumberField F := numberFieldTowerAbstractBaseNumberField K L
  letI : NumberField E := numberFieldTowerAbstractTopNumberField K L
  let eBase : K ≃ₐ[ℚ] F := numberFieldTowerAbstractBaseFieldEquiv K L
  let eTop : L ≃ₐ[ℚ] E := numberFieldTowerAbstractTopFieldEquiv K L
  have hcompat : ∀ x : K,
      eTop (algebraMap K L x) = algebraMap F E (eBase x) :=
    numberFieldTowerAbstractFieldEquiv_algebraMap K L
  let actualFieldEquiv :
      (IdeleClassGroup K ⧸ (_root_.ideleClassNorm K L).range) ≃*
        (IdeleClassGroup F ⧸ (_root_.ideleClassNorm F E).range) :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (K := K) (L := L) (K' := F) (L' := E) eBase eTop hcompat
  exact
    Additive.ofMul
      (actualFieldEquiv.symm
          (QuotientGroup.mk'
            (_root_.ideleClassNorm F E).range
            (Additive.toMul
              ((rationalAbstractFixedFieldIdeleClassEquivFixed H).symm a))))

theorem numberFieldTowerFiniteNormClassDirectComparison_eq_actualValue
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)) :
    numberFieldTowerFiniteNormClassDirectComparisonValue K L a =
      numberFieldTowerActualNormClassRepresentativeValue K L a := by
  rfl

theorem numberFieldTowerActualNormClassRepresentativeValue_eq_expected
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)) :
    numberFieldTowerActualNormClassRepresentativeValue K L a =
      numberFieldTowerFiniteNormClassExpectedValue K L a := by
  rfl

/-- On a finite norm-class representative, the comparison with the
original number-field tower is the ordinary class map applied after
transporting the fixed-field idele class back to `K`. -/
@[simp]
theorem
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)) :
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient K L
        (finiteNormClass rationalIdeleClassRepresentation
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L) a) =
      Additive.ofMul
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range
          (Additive.toMul
            ((numberFieldTowerIdeleClassEquivAmbientFixed K L).symm
              a))) := by
  rfl

/-- On an idele class of the original base field, the fixed-part
realization followed by the abstract finite norm-class map is exactly
the genuine quotient class modulo the ordinary idele-class norm. -/
@[simp]
theorem
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
    (c : IdeleClassGroup K) :
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient K L
        (finiteNormClass rationalIdeleClassRepresentation
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
          (numberFieldTowerIdeleClassEquivAmbientFixed K L
            (Additive.ofMul c))) =
      Additive.ofMul
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range c) := by
  simpa only [
    AddEquiv.symm_apply_apply, toMul_ofMul] using
    (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
      K L
      (numberFieldTowerIdeleClassEquivAmbientFixed K L
        (Additive.ofMul c)))

/-- Under the compatible rational-separable-closure realization of a
finite Galois number-field extension, the abstract finite norm subgroup
is exactly the ordinary idele-class norm subgroup of the original
extension. -/
theorem
    map_numberFieldTowerFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange :
    letI := (numberFieldTowerFiniteAbstractField K L).finite
    letI := numberFieldTowerExtensionSubgroup_normal K L
    letI := numberFieldTowerExtensionQuotient_finite K L
    (finiteNormSubgroup rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).map
        (numberFieldTowerIdeleClassEquivAmbientFixed
          K L).symm.toAddMonoidHom =
      (_root_.ideleClassNorm K L).range.toAddSubgroup := by
  let E :=
    numberFieldTowerIdeleClassEquivAmbientFixed K L
  let Q :=
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
      K L
  ext c
  constructor
  · rintro ⟨a, ha, rfl⟩
    have haZero :
        finiteNormClass rationalIdeleClassRepresentation
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L) a =
          0 :=
      by simp_all
    have hclass :=
      numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
        K L (Additive.toMul (E.symm a))
    have hmk :
        QuotientGroup.mk'
            (_root_.ideleClassNorm K L).range
            (Additive.toMul (E.symm a)) =
          1 := by
      have hzero :
          (0 : Additive
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range)) =
            Additive.ofMul
              (QuotientGroup.mk'
                (_root_.ideleClassNorm K L).range
                (Additive.toMul (E.symm a))) := by
        simpa only [E, ofMul_toMul,
          AddEquiv.apply_symm_apply, haZero, map_zero] using hclass
      exact congrArg Additive.toMul hzero.symm
    exact
      (QuotientGroup.eq_one_iff
        (Additive.toMul (E.symm a))).1 hmk
  · intro hc
    refine ⟨E c, ?_, E.symm_apply_apply c⟩
    apply
      (finiteNormClass_eq_zero_iff
        rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
        (E c)).1
    apply Q.injective
    have hmk :
        QuotientGroup.mk'
            (_root_.ideleClassNorm K L).range
            (Additive.toMul c) =
          1 :=
      by simp_all
    have hclass :=
      numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
        K L (Additive.toMul c)
    simpa only [E, ofMul_toMul,
      hmk, ofMul_one, map_zero] using hclass

/-- If an ordinary subgroup contains the norm subgroup of a finite Galois
number-field extension, then its transport to the compatible rational
absolute fixed part is open for the genuine norm topology. -/
theorem numberFieldTowerTransport_isNormOpen_of_normRange_le
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    letI := (numberFieldTowerFiniteAbstractField K L).finite
    IsNormOpen rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      ((H.toAddSubgroup).map
        (numberFieldTowerIdeleClassEquivAmbientFixed
          K L).toAddMonoidHom :
        AddSubgroup
          (KummerTheory.ambientFixedAddSubgroup
            rationalIdeleClassRepresentation
            (numberFieldTowerBaseSubgroup K L))) := by
  let E :=
    numberFieldTowerIdeleClassEquivAmbientFixed K L
  rw [normTopology_addSubgroup_isOpen_iff]
  refine
    ⟨numberFieldTowerFiniteGaloisSubextension K L, ?_⟩
  intro a ha
  have hback :
      E.symm a ∈
        (finiteNormSubgroup rationalIdeleClassRepresentation
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).map
            E.symm.toAddMonoidHom :=
    ⟨a, ha, rfl⟩
  have hnorm :
      Additive.toMul (E.symm a) ∈
        (_root_.ideleClassNorm K L).range := by
    rw [
      map_numberFieldTowerFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange
        K L] at hback
    exact hback
  exact
    ⟨E.symm a, hLH hnorm, E.apply_symm_apply a⟩
