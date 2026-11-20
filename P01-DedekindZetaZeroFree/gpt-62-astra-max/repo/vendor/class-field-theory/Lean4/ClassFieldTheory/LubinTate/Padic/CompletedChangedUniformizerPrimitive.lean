module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveAction

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Primitive changed-uniformizer points in the completed p-adic level

For a p-adic valuation-ring unit `u`, the primitive polynomial attached to
the changed uniformizer `u * p` remains Eisenstein after extension to the
completed-unramified Witt valuation ring.  Consequently the genuine theta
value constructed in the standard completed level has the changed
primitive polynomial as its minimal polynomial and generates the whole
completed level over the completed-unramified coefficient field.
-/

noncomputable section

open scoped Polynomial

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField

section

variable (p : ℕ) [Fact p.Prime] (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)

/-- The integral primitive polynomial for the changed uniformizer `u * p`
over the completed-unramified Witt valuation ring. -/
noncomputable def padicChangedCompletedPrimitivePolynomialInteger :
    Polynomial
      (padicCompletedUnramifiedCompleteDVF p).valuationSubring :=
  (standardLubinTatePrimitivePolynomial
      (padicLocalField p)
      (standardLubinTateChangedUniformizer
        (padicLocalField p)
        (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map
    (padicCompletedUnramifiedIntegerMap p)

/-- The field-valued changed primitive polynomial after extension from
`ℚ_[p]` to the completed-unramified fraction field. -/
noncomputable def padicChangedCompletedPrimitivePolynomial :
    Polynomial (padicCompletedUnramifiedField p) :=
  (standardLubinTatePrimitivePolynomialOverField
      (padicLocalField p)
      (standardLubinTateChangedUniformizer
        (padicLocalField p)
        (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map
    (algebraMap ℚ_[p] (padicCompletedUnramifiedField p))

/-- Passing the integral changed primitive polynomial to the fraction field
gives the field-valued changed primitive polynomial. -/
theorem padicChangedCompletedPrimitivePolynomialInteger_map :
    (padicChangedCompletedPrimitivePolynomialInteger p u n).map
        (algebraMap
          (padicCompletedUnramifiedCompleteDVF p).valuationSubring
          (padicCompletedUnramifiedField p)) =
      padicChangedCompletedPrimitivePolynomial p u n := by
  let O := (padicLocalField p).valuationSubring
  let A := (padicCompletedUnramifiedCompleteDVF p).valuationSubring
  let E := padicCompletedUnramifiedField p
  let Q :=
    standardLubinTatePrimitivePolynomial
      (padicLocalField p) (standardLubinTateChangedUniformizer
        (padicLocalField p)
        (padicIntEquivValuationSubring p p) u) n
  have hmaps :
      (algebraMap A E).comp
          (padicCompletedUnramifiedIntegerMap p) =
        (algebraMap ℚ_[p] E).comp (algebraMap O ℚ_[p]) := by
    ext z
    exact padicCompletedUnramifiedIntegerMap_coe p z
  change
    (Q.map (padicCompletedUnramifiedIntegerMap p)).map
        (algebraMap A E) =
      (Q.map (algebraMap O ℚ_[p])).map
        (algebraMap ℚ_[p] E)
  rw [Polynomial.map_map, Polynomial.map_map, hmaps]

/-- The integral changed primitive polynomial is monic. -/
theorem padicChangedCompletedPrimitivePolynomialInteger_monic :
    (padicChangedCompletedPrimitivePolynomialInteger p u n).Monic :=
  (standardLubinTatePrimitivePolynomial_monic
    (padicLocalField p)
    (standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map _

/-- The field-valued changed primitive polynomial is monic. -/
theorem padicChangedCompletedPrimitivePolynomial_monic :
    (padicChangedCompletedPrimitivePolynomial p u n).Monic :=
  (standardLubinTatePrimitivePolynomialOverField_monic
    (padicLocalField p)
    (standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map _

/-- The integral changed primitive polynomial has degree
`(p - 1) * p ^ n`. -/
theorem padicChangedCompletedPrimitivePolynomialInteger_natDegree :
    (padicChangedCompletedPrimitivePolynomialInteger p u n).natDegree =
      (p - 1) * p ^ n := by
  have hcard :
      Nat.card (padicLocalField p).residueField = p := by
    simpa [padicLocalField] using
      padicCompleteDVF_residueField_card p
  rw [padicChangedCompletedPrimitivePolynomialInteger,
    (standardLubinTatePrimitivePolynomial_monic
      (padicLocalField p)
      (standardLubinTateChangedUniformizer
        (padicLocalField p)
        (padicIntEquivValuationSubring p p) u) n).natDegree_map,
    standardLubinTatePrimitivePolynomial_natDegree, hcard]

/-- The changed primitive polynomial has degree `(p - 1) * p ^ n`. -/
theorem padicChangedCompletedPrimitivePolynomial_natDegree :
    (padicChangedCompletedPrimitivePolynomial p u n).natDegree =
      (p - 1) * p ^ n := by
  have hcard :
      Nat.card (padicLocalField p).residueField = p := by
    simpa [padicLocalField] using
      padicCompleteDVF_residueField_card p
  simp [padicChangedCompletedPrimitivePolynomial, standardLubinTatePrimitivePolynomialOverField_natDegree, hcard]

end

/-- The image of the changed uniformizer `u * p` is a uniformizer of the
completed-unramified coefficient field. -/
theorem padicChangedCompletedUniformizer_isUniformizer
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    let π :=
      padicIntEquivValuationSubring p (p : ℤ_[p])
    let πu :=
      standardLubinTateChangedUniformizer
        (padicLocalField p) π u
    (padicCompletedUnramifiedCompleteDVF p).valuation.IsUniformizer
      ((padicCompletedUnramifiedIntegerMap p πu :
        (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
          padicCompletedUnramifiedField p) := by
  let target := padicCompletedUnramifiedCompleteDVF p
  let π := padicIntEquivValuationSubring p p
  let πE :=
    padicCompletedUnramifiedIntegerMap p π
  let uE :=
    padicCompletedUnramifiedIntegerMap p
      u
  have hπ :
      target.valuation.IsUniformizer
        πE := by
    simpa only [target, π, πE] using
      padicCompletedUnramifiedIntegerMap_isUniformizer p
  apply hπ.of_associated
  have hmul : padicCompletedUnramifiedIntegerMap p (standardLubinTateChangedUniformizer
    (padicLocalField p) π u) = uE * πE :=
    map_mul (padicCompletedUnramifiedIntegerMap p)
      (u : (padicLocalField p).valuationSubring) π
  exact hmul.symm ▸ (associated_unit_mul_right πE uE (u.isUnit.map (padicCompletedUnramifiedIntegerMap p)))

variable (p : ℕ) [Fact p.Prime] (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)

/-- The integral changed primitive polynomial is weakly Eisenstein after
base change to the completed-unramified valuation ring. -/
theorem
    padicChangedCompletedPrimitivePolynomialInteger_isWeaklyEisensteinAt :
    (padicChangedCompletedPrimitivePolynomialInteger p u n).IsWeaklyEisensteinAt
      (padicCompletedUnramifiedCompleteDVF p).maximalIdeal := by
  rw [← padicCompletedUnramifiedIntegerMap_map_maximalIdeal p]
  exact
    (standardLubinTatePrimitivePolynomial_isEisensteinAt
      (standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u)
      n).isWeaklyEisensteinAt.map
        (padicCompletedUnramifiedIntegerMap p)

/-- The integral changed primitive polynomial is genuinely Eisenstein over
the completed-unramified valuation ring. -/
theorem padicChangedCompletedPrimitivePolynomialInteger_isEisensteinAt :
    (padicChangedCompletedPrimitivePolynomialInteger p u n).IsEisensteinAt
      (padicCompletedUnramifiedCompleteDVF p).maximalIdeal := by
  let target := padicCompletedUnramifiedCompleteDVF p
  let π := padicIntEquivValuationSubring p p
  let πu :=
    standardLubinTateChangedUniformizer
      (padicLocalField p) π u
  let πuE :=
    padicCompletedUnramifiedIntegerMap p πu
  refine (padicChangedCompletedPrimitivePolynomialInteger_monic p u n).isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal target.valuationSubring).ne_top
    ?_ ?_
  · intro i hi
    exact
      (padicChangedCompletedPrimitivePolynomialInteger_isWeaklyEisensteinAt
        p u n).mem hi
  · have hπu :
        target.valuation.IsUniformizer
          πuE := by
      simpa only [target, π, πu, πuE] using
        padicChangedCompletedUniformizer_isUniformizer p u
    simpa only [padicChangedCompletedPrimitivePolynomialInteger,
      Polynomial.coeff_map,
      standardLubinTatePrimitivePolynomial_coeff_zero,
      π, πu, πuE] using (target.uniformizer_not_mem_maximalIdeal_sq hπu)

/-- The integral changed primitive polynomial is irreducible. -/
theorem padicChangedCompletedPrimitivePolynomialInteger_irreducible :
    Irreducible
      (padicChangedCompletedPrimitivePolynomialInteger p u n) := by
  apply
    (padicChangedCompletedPrimitivePolynomialInteger_isEisensteinAt
      p u n).irreducible
      (IsLocalRing.maximalIdeal.isMaximal
        (padicCompletedUnramifiedCompleteDVF p).valuationSubring).isPrime
      (padicChangedCompletedPrimitivePolynomialInteger_monic
        p u n).isPrimitive
  rw [padicChangedCompletedPrimitivePolynomialInteger_natDegree]
  exact Nat.mul_pos (Nat.sub_pos_of_lt (Nat.Prime.one_lt Fact.out)) (Nat.pow_pos (Nat.Prime.pos Fact.out))

/-- The changed primitive polynomial remains irreducible over the completed
maximal-unramified fraction field. -/
theorem padicChangedCompletedPrimitivePolynomial_irreducible :
    Irreducible (padicChangedCompletedPrimitivePolynomial p u n) := by
  have hmap :
      Irreducible
        ((padicChangedCompletedPrimitivePolynomialInteger p u n).map
          (algebraMap
            (padicCompletedUnramifiedCompleteDVF p).valuationSubring
            (padicCompletedUnramifiedField p))) := by
    exact (padicChangedCompletedPrimitivePolynomialInteger_monic p u n).irreducible_iff_irreducible_map_fraction_map.mp
        (padicChangedCompletedPrimitivePolynomialInteger_irreducible
          p u n)
  rwa [padicChangedCompletedPrimitivePolynomialInteger_map] at hmap

/-- The theta value is a root of the named changed primitive polynomial
over the completed-unramified field. -/
theorem padicChangedUniformizerThetaValue_isRoot_completedPrimitivePolynomial :
    ((padicChangedCompletedPrimitivePolynomial p u n).map
      (algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n))).IsRoot
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) := by
  simpa only [padicChangedCompletedPrimitivePolynomial,
    Polynomial.map_map,
    IsScalarTower.algebraMap_eq ℚ_[p]
      (padicCompletedUnramifiedField p) (padicCompletedLevelField p n)]
    using
    padicChangedUniformizerThetaValue_field_isRoot p u n

/-- The theta value is integral over the completed-unramified field. -/
theorem padicChangedUniformizerThetaValue_isIntegral_completedBase :
    IsIntegral (padicCompletedUnramifiedField p)
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) := by
  apply Algebra.IsIntegral.isIntegral

/-- The minimal polynomial of the theta value over the completed-unramified
field is the genuine changed primitive polynomial. -/
theorem padicChangedUniformizerThetaValue_minpoly_completedBase :
    minpoly (padicCompletedUnramifiedField p)
        ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n) =
      padicChangedCompletedPrimitivePolynomial p u n := by
  have hroot :
      Polynomial.aeval
          ((padicChangedUniformizerThetaValue p u n :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
              padicCompletedLevelField p n)
          (padicChangedCompletedPrimitivePolynomial p u n) =
        0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact
      padicChangedUniformizerThetaValue_isRoot_completedPrimitivePolynomial
        p u n
  have hmin :=
    minpoly.eq_of_irreducible
      (padicChangedCompletedPrimitivePolynomial_irreducible p u n)
      hroot
  rw [(padicChangedCompletedPrimitivePolynomial_monic
    p u n).leadingCoeff, inv_one, Polynomial.C_1, mul_one] at hmin
  exact hmin.symm

/-- The fixed theta point generates the entire standard completed level
over the completed-unramified coefficient field. -/
theorem padicChangedUniformizerThetaValue_adjoin_completedBase_eq_top :
    IntermediateField.adjoin
        (padicCompletedUnramifiedField p)
        ({((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n)} :
          Set (padicCompletedLevelField p n)) =
      ⊤ := by
  apply
    (Field.primitive_element_iff_minpoly_natDegree_eq
      (padicCompletedUnramifiedField p)
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n)).2
  rw [padicChangedUniformizerThetaValue_minpoly_completedBase,
    padicChangedCompletedPrimitivePolynomial_natDegree]
  let pb := padicCompletedPrimitivePowerBasis p n
  calc
    _ =
        (padicCompletedPrimitivePolynomial p n).natDegree :=
      (padicCompletedPrimitivePolynomial_natDegree p n).symm
    _ =
        (minpoly (padicCompletedUnramifiedField p) pb.gen).natDegree := by
      rw [show pb.gen = padicCompletedPrimitiveRoot p n by
        rfl]
      rw [padicCompletedPrimitiveRoot_minpoly]
    _ = pb.dim := pb.natDegree_minpoly
    _ =
        Module.finrank (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) :=
      pb.finrank.symm

/-- The theta value supplies a power basis of the completed standard level
over the completed-unramified field. -/
noncomputable def padicChangedUniformizerThetaPowerBasis :
    PowerBasis (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) := by
  apply PowerBasis.ofAdjoinEqTop
    (padicChangedUniformizerThetaValue_isIntegral_completedBase p u n)
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (padicChangedUniformizerThetaValue_isIntegral_completedBase
        p u n).isAlgebraic,
    padicChangedUniformizerThetaValue_adjoin_completedBase_eq_top,
    IntermediateField.top_toSubalgebra]

/-- The generator of the theta power basis is the genuine evaluated theta
value. -/
@[simp]
theorem padicChangedUniformizerThetaPowerBasis_gen :
    (padicChangedUniformizerThetaPowerBasis p u n).gen =
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) :=
  PowerBasis.ofAdjoinEqTop_gen _ _

end LubinTate

end
