module

public import ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.CompletedCoefficientEvaluation
public import ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.CompletedPrimitivePoint
public import ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.CompletedScalarEndomorphism
public import ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.FiniteLevelEvaluation
public import ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.FiniteLevelPrimitiveRoot
public import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.CompletedSeries
public import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.DefectCorrection
public import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.IntertwinerConstruction
public import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.ScalarCompatibility
public import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.ScalarEndomorphisms

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Changed-uniformizer evaluation on completed p-adic levels

This endpoint evaluates the genuine changed-uniformizer intertwiner at the
completed multiplicative primitive point.  It proves the exact scalar,
Frobenius, root, and level-embedding identities used by the completed
Lubin--Tate tower.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

attribute [local instance 50]
  padicCompletedMultiplicativeWittUniformSpace

attribute [local instance]
  padicCompletedMultiplicativeTargetWithIdeal
  padicCompletedMultiplicativeTargetCompleteSpace
  padicCompletedMultiplicativeTargetT2Space

section

variable (p : ℕ) [Fact p.Prime] (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)

/-- The changed-uniformizer theta value at the genuine completed
multiplicative primitive point. -/
noncomputable def padicChangedUniformizerThetaValue :
    (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  padicCompletedLevelPowerSeriesEval p n
    (padicCompletedMultiplicativePrimitivePoint p n)
    (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
    (padicChangedUniformizerIntertwiner p u)

/-- The changed-uniformizer theta value is topologically nilpotent. -/
theorem padicChangedUniformizerThetaValue_hasEval :
    PowerSeries.HasEval (padicChangedUniformizerThetaValue p u n) := padicCompletedLevelPowerSeriesEval_hasEval p n
      (padicCompletedMultiplicativePrimitivePoint p n)
      (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
      (padicChangedUniformizerIntertwiner p u)
      (padicChangedUniformizerIntertwiner_hasSubst p u)

end

section

variable (p : ℕ) [Fact p.Prime] (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring) (hx : PowerSeries.HasEval x)

/-- Analytic action of a completed changed-standard scalar endomorphism. -/
noncomputable def padicCompletedChangedStandardScalarEndomorphismValue
    (a : (padicLocalField p).valuationSubring) :
    (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  padicCompletedLevelPowerSeriesEval p n x hx
    (padicCompletedChangedStandardScalarEndomorphism p u a)

/-- A completed changed-standard scalar value remains a convergent
evaluation point. -/
theorem padicCompletedChangedStandardScalarEndomorphismValue_hasEval
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.HasEval
      (padicCompletedChangedStandardScalarEndomorphismValue
        p u n x hx a) :=
  padicCompletedLevelPowerSeriesEval_hasEval p n x hx
    (padicCompletedChangedStandardScalarEndomorphism p u a)
    (padicCompletedChangedStandardScalarEndomorphism_hasSubst p u a)

/-- Multiplication of changed-standard scalars is composition of their
completed analytic actions. -/
theorem padicCompletedChangedStandardScalarEndomorphismValue_mul
    (a b : (padicLocalField p).valuationSubring) :
    padicCompletedChangedStandardScalarEndomorphismValue
        p u n x hx (a * b) =
      padicCompletedChangedStandardScalarEndomorphismValue p u n
        (padicCompletedChangedStandardScalarEndomorphismValue
          p u n x hx b)
        (padicCompletedChangedStandardScalarEndomorphismValue_hasEval
          p u n x hx b) a := by
  rw [padicCompletedChangedStandardScalarEndomorphismValue,
    padicCompletedChangedStandardScalarEndomorphism_mul]
  exact
    padicCompletedLevelPowerSeriesEval_subst p n x hx
      (padicCompletedChangedStandardScalarEndomorphism p u b)
      (padicCompletedChangedStandardScalarEndomorphism p u a)
      (padicCompletedChangedStandardScalarEndomorphism_hasSubst p u b)
      ((by apply padicCompletedChangedStandardScalarEndomorphismValue_hasEval))

/-- The scalar `1` fixes every completed changed-standard evaluation
point. -/
@[simp]
theorem padicCompletedChangedStandardScalarEndomorphismValue_one :
    padicCompletedChangedStandardScalarEndomorphismValue
        p u n x hx 1 =
      x := by
  simp [padicCompletedChangedStandardScalarEndomorphismValue]

/-- Evaluating a power of the changed uniformizer is evaluation of the
corresponding changed standard division-polynomial iterate. -/
theorem
    padicCompletedChangedStandardScalarEndomorphismValue_uniformizer_pow (r : ℕ) :
    padicCompletedChangedStandardScalarEndomorphismValue p u n x hx
        ((standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) ^ r) =
      Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (standardLubinTateChangedUniformizer
            (padicLocalField p)
            (padicIntEquivValuationSubring p (p : ℤ_[p])) u) r) := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let πu :=
    standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p p) u
  change
    padicCompletedChangedStandardScalarEndomorphismValue
        p u n x hx (πu ^ r) =
      Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x
        (standardLubinTatePolynomialIterate
          (padicLocalField p) πu r)
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [pow_succ',
        padicCompletedChangedStandardScalarEndomorphismValue_mul]
      rw [padicCompletedChangedStandardScalarEndomorphismValue,
        padicCompletedChangedStandardScalarEndomorphism_uniformizer,
        padicCompletedChangedStandardSeries,
        ← standardLubinTatePolynomial_toPowerSeries_eq_series hπ,
        padicCompletedLevelPowerSeriesEval_map_polynomial,
        ih,
        standardLubinTatePolynomialIterate_succ,
        Polynomial.eval₂_comp]

end

section

variable (p : ℕ) [Fact p.Prime] (u : (padicLocalField p).valuationSubringˣ)

/-- Genuine completed-level evaluation of the changed-uniformizer scalar
intertwining identity. -/
theorem padicChangedUniformizerIntertwiner_endomorphism_evaluation
    (a : (padicLocalField p).valuationSubring) (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    padicCompletedLevelPowerSeriesEval p n
        (padicCompletedMultiplicativeScalarEndomorphismValue
          p n x hx a)
        (padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
          p n x hx a)
        (padicChangedUniformizerIntertwiner p u) =
      padicCompletedChangedStandardScalarEndomorphismValue p u n
        (padicCompletedLevelPowerSeriesEval p n x hx
          (padicChangedUniformizerIntertwiner p u))
        (padicCompletedLevelPowerSeriesEval_hasEval p n x hx
          (padicChangedUniformizerIntertwiner p u)
          (padicChangedUniformizerIntertwiner_hasSubst p u))
        a := by
  let M := padicCompletedMultiplicativeScalarEndomorphism p a
  let H := padicChangedUniformizerIntertwiner p u
  let S := padicCompletedChangedStandardScalarEndomorphism p u a
  let xM :=
    padicCompletedMultiplicativeScalarEndomorphismValue p n x hx a
  let xH := padicCompletedLevelPowerSeriesEval p n x hx H
  let hxM :=
    padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
      p n x hx a
  let hxH :=
    padicCompletedLevelPowerSeriesEval_hasEval p n x hx H
      (padicChangedUniformizerIntertwiner_hasSubst p u)
  calc
    _ =
        padicCompletedLevelPowerSeriesEval p n x hx
          (PowerSeries.subst M H) := (padicCompletedLevelPowerSeriesEval_subst p n x hx
          M H
          (padicCompletedMultiplicativeScalarEndomorphism_hasSubst p a)
          hxM).symm
    _ =
        padicCompletedLevelPowerSeriesEval p n x hx
          (PowerSeries.subst H S) := by
      rw [padicChangedUniformizerIntertwiner_endomorphism]
    _ =
        padicCompletedLevelPowerSeriesEval p n xH hxH S := padicCompletedLevelPowerSeriesEval_subst p n x hx
          H S (padicChangedUniformizerIntertwiner_hasSubst p u) hxH

/-- Evaluation of the changed-uniformizer intertwiner is injective on
topologically nilpotent completed-level integers.  Its inverse is the
formal substitution inverse determined by the genuine Witt-unit linear
coefficient. -/
theorem padicChangedUniformizerIntertwiner_eval_injective (n : ℕ)
    {x y : (padicCompletedLevelCompleteDVF p n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy :
      padicCompletedLevelPowerSeriesEval p n x hx
          (padicChangedUniformizerIntertwiner p u) =
        padicCompletedLevelPowerSeriesEval p n y hy
          (padicChangedUniformizerIntertwiner p u)) :
    x = y := by
  apply
    padicCompletedLevelPowerSeriesEval_injective_of_unitLinearCoefficient
      p n (padicChangedUniformizerIntertwiner p u)
      (padicChangedUniformizerIntertwiner_constantCoeff p u)
      ?_ hx hy hxy
  rw [padicChangedUniformizerIntertwiner_coeff_one]
  exact (padicChangedUniformizerLinearCoefficient p u).isUnit

/-- The changed-uniformizer intertwiner evaluates to zero at the zero
point. -/
theorem padicChangedUniformizerIntertwiner_eval_zero (n : ℕ) :
    padicCompletedLevelPowerSeriesEval p n
        0 PowerSeries.HasEval.zero
        (padicChangedUniformizerIntertwiner p u) =
      0 := by
  obtain ⟨B, hB⟩ :
      PowerSeries.X ∣
        padicChangedUniformizerIntertwiner p u := by
    rw [PowerSeries.X_dvd_iff]
    apply padicChangedUniformizerIntertwiner_constantCoeff
  simp [hB]

/-- The changed-uniformizer theta value is killed by the `n + 1`-fold
changed standard division-polynomial iterate. -/
theorem padicChangedUniformizerThetaValue_iterate_succ_eq_zero (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicChangedUniformizerThetaValue p u n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (standardLubinTateChangedUniformizer
            (padicLocalField p)
            (padicIntEquivValuationSubring p (p : ℤ_[p])) u)
          (n + 1)) =
      0 := by
  let π :=
    padicIntEquivValuationSubring p p
  let πu :=
    standardLubinTateChangedUniformizer
      (padicLocalField p) π u
  change
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicChangedUniformizerThetaValue p u n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p) πu (n + 1)) =
      0
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  let xChanged :=
    padicCompletedMultiplicativeScalarEndomorphismValue
      p n x hx (πu ^ (n + 1))
  let hxChanged :=
    padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
      p n x hx (πu ^ (n + 1))
  have hxChangedZero : xChanged = 0 := by
    change
      padicCompletedMultiplicativeScalarEndomorphismValue p n
          (padicCompletedMultiplicativePrimitivePoint p n)
          (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
          ((standardLubinTateChangedUniformizer
            (padicLocalField p)
            (padicIntEquivValuationSubring p p) u) ^
              (n + 1)) =
        0
    exact
      padicCompletedMultiplicativePrimitivePoint_changedUniformizer_pow_succ_eq_zero
        p u n
  have hleftZero :
      padicCompletedLevelPowerSeriesEval p n xChanged hxChanged
          (padicChangedUniformizerIntertwiner p u) =
        0 := by
    calc
      _ =
          padicCompletedLevelPowerSeriesEval p n
            0 PowerSeries.HasEval.zero
            (padicChangedUniformizerIntertwiner p u) :=
        padicCompletedLevelPowerSeriesEval_congr_point p n
          hxChanged PowerSeries.HasEval.zero hxChangedZero
          (padicChangedUniformizerIntertwiner p u)
      _ = 0 :=
        padicChangedUniformizerIntertwiner_eval_zero p u n
  have hpow :
      padicCompletedChangedStandardScalarEndomorphismValue p u n
          (padicChangedUniformizerThetaValue p u n)
          (padicChangedUniformizerThetaValue_hasEval p u n)
          (πu ^ (n + 1)) =
        Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (padicChangedUniformizerThetaValue p u n)
          (standardLubinTatePolynomialIterate
            (padicLocalField p) πu (n + 1)) := by
    simpa only [π, πu] using
      (padicCompletedChangedStandardScalarEndomorphismValue_uniformizer_pow
        p u n
        (padicChangedUniformizerThetaValue p u n)
        (padicChangedUniformizerThetaValue_hasEval p u n)
        (n + 1))
  exact hpow.symm.trans ((padicChangedUniformizerIntertwiner_endomorphism_evaluation
    p u (πu ^ (n + 1)) n x hx).symm.trans hleftZero)

/-- The changed-uniformizer theta value is not killed one level early. -/
theorem padicChangedUniformizerThetaValue_iterate_ne_zero (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicChangedUniformizerThetaValue p u n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (standardLubinTateChangedUniformizer
            (padicLocalField p)
            (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n) ≠
      0 := by
  let π :=
    padicIntEquivValuationSubring p p
  let πu :=
    standardLubinTateChangedUniformizer
      (padicLocalField p) π u
  change
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicChangedUniformizerThetaValue p u n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p) πu n) ≠
      0
  intro hzero
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  let xChanged :=
    padicCompletedMultiplicativeScalarEndomorphismValue
      p n x hx (πu ^ n)
  let hxChanged :=
    padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
      p n x hx (πu ^ n)
  have hpow :
      padicCompletedChangedStandardScalarEndomorphismValue p u n
          (padicChangedUniformizerThetaValue p u n)
          (padicChangedUniformizerThetaValue_hasEval p u n)
          (πu ^ n) =
        Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (padicChangedUniformizerThetaValue p u n)
          (standardLubinTatePolynomialIterate
            (padicLocalField p) πu n) := by
    simpa only [π, πu] using
      (padicCompletedChangedStandardScalarEndomorphismValue_uniformizer_pow
        p u n
        (padicChangedUniformizerThetaValue p u n)
        (padicChangedUniformizerThetaValue_hasEval p u n) n)
  have hleftZero := (padicChangedUniformizerIntertwiner_endomorphism_evaluation
      p u (πu ^ n) n x hx).trans (hpow.trans hzero)
  have hxChangedZero : xChanged = 0 := by
    apply padicChangedUniformizerIntertwiner_eval_injective
      p u n hxChanged PowerSeries.HasEval.zero
    exact hleftZero.trans
      (padicChangedUniformizerIntertwiner_eval_zero p u n).symm
  apply
    padicCompletedMultiplicativePrimitivePoint_changedUniformizer_pow_ne_zero
      p u n
  exact hxChangedZero

end

/-- The changed-uniformizer theta value is an actual root of the genuine
changed primitive Lubin--Tate polynomial in the completed level. -/
theorem padicChangedUniformizerThetaValue_isRoot
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    ((standardLubinTatePrimitivePolynomial
        (padicLocalField p)
        (standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map
      (padicCompletedLevelPadicIntegerCoefficientHom p n)).IsRoot
        (padicChangedUniformizerThetaValue p u n) := by
  let F := padicLocalField p
  let πu :=
    standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p p) u
  let φ := padicCompletedLevelPadicIntegerCoefficientHom p n
  let theta := padicChangedUniformizerThetaValue p u n
  have hfactor :=
    congrArg (Polynomial.eval₂ φ theta)
      (standardLubinTatePolynomialIterate_succ_factor F πu n)
  rw [Polynomial.eval₂_mul,
    padicChangedUniformizerThetaValue_iterate_succ_eq_zero p u n]
      at hfactor
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  exact (mul_eq_zero.mp hfactor.symm).resolve_left
    (padicChangedUniformizerThetaValue_iterate_ne_zero p u n)

variable (p : ℕ) [Fact p.Prime] (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)

/-- Field-valued form of the changed primitive-root equation. -/
theorem padicChangedUniformizerThetaValue_field_isRoot :
    ((standardLubinTatePrimitivePolynomialOverField
        (padicLocalField p)
        (standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map
      (algebraMap ℚ_[p] (padicCompletedLevelField p n))).IsRoot
        ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n) := by
  let F := padicLocalField p
  let πu :=
    standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p p) u
  let Q := standardLubinTatePrimitivePolynomial F πu n
  let theta := padicChangedUniformizerThetaValue p u n
  have hinteger :
      Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          theta Q =
        0 := by
    simpa only [Polynomial.IsRoot, Polynomial.eval_map, F, πu, Q, theta]
      using (padicChangedUniformizerThetaValue_isRoot p u n)
  have hcoe := congrArg
    (fun z : (padicCompletedLevelCompleteDVF p n).valuationSubring =>
      (z : padicCompletedLevelField p n)) hinteger
  have hfield :
      Polynomial.eval₂
          (padicCompletedLevelPadicFieldCoefficientHom p n)
          (theta : padicCompletedLevelField p n) Q =
        0 := by
    change
      ((Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          theta Q :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) =
        0 at hcoe
    rw [padicCompletedLevelPadicIntegerPolynomialEval_coe] at hcoe
    exact hcoe
  rw [standardLubinTatePrimitivePolynomialOverField,
    Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_map]
  change
    Polynomial.eval₂
        (padicCompletedLevelPadicFieldCoefficientHom p n)
        theta Q =
      0
  exact hfield

/-- The theta value annihilates the minimal polynomial of the canonical
generator of the changed finite Lubin--Tate level. -/
theorem padicChangedUniformizerThetaValue_aeval_levelMinpoly :
    let hπ :=
      standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u
    Polynomial.aeval
        ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n)
        (minpoly ℚ_[p] (standardLubinTateLevelPowerBasis hπ n).gen) =
      0 := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  change
    Polynomial.aeval
        ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n)
        (minpoly ℚ_[p] (standardLubinTateLevelPowerBasis hπ n).gen) =
      0
  rw [standardLubinTateLevelPowerBasis_minpoly hπ n,
    Polynomial.aeval_def]
  simpa [Polynomial.eval_map] using
    padicChangedUniformizerThetaValue_field_isRoot p u n

/-- The genuine embedding of the changed finite Lubin--Tate level into
the completed standard level, sending its canonical generator to theta. -/
noncomputable def padicChangedUniformizerLevelEmbedding :
    let hπ :=
      standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u
    standardLubinTateLevelField hπ n →ₐ[ℚ_[p]]
      padicCompletedLevelField p n := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let theta :=
    ((padicChangedUniformizerThetaValue p u n :
      (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)
  change
    standardLubinTateLevelField hπ n →ₐ[ℚ_[p]]
      padicCompletedLevelField p n
  exact
    (standardLubinTateLevelPowerBasis hπ n).lift theta
      (by
        simpa using
          padicChangedUniformizerThetaValue_aeval_levelMinpoly p u n)

/-- The changed-level embedding sends the canonical power-basis generator
to the actual theta value. -/
@[simp]
theorem padicChangedUniformizerLevelEmbedding_apply_gen :
    let hπ :=
      standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u
    padicChangedUniformizerLevelEmbedding p u n
        (standardLubinTateLevelPowerBasis hπ n).gen =
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let theta :=
    ((padicChangedUniformizerThetaValue p u n :
      (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)
  change
    (standardLubinTateLevelPowerBasis hπ n).lift
        theta
        (padicChangedUniformizerThetaValue_aeval_levelMinpoly p u n)
        (standardLubinTateLevelPowerBasis hπ n).gen =
      theta
  exact
    (standardLubinTateLevelPowerBasis hπ n).lift_gen _ _

/-- Evaluating Frobenius on the coefficients of the changed-uniformizer
intertwiner is the same as first applying the multiplicative unit
endomorphism to the evaluation point and then evaluating the original
intertwiner. -/
theorem padicChangedUniformizerIntertwiner_frobenius_evaluation
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    padicCompletedLevelPowerSeriesEval p n x hx
        (PowerSeries.map WittVector.frobenius
          (padicChangedUniformizerIntertwiner p u)) =
      padicCompletedLevelPowerSeriesEval p n
        (padicCompletedLevelPowerSeriesEval p n x hx
          (padicCompletedMultiplicativeUnitEndomorphism p u))
        (padicCompletedLevelPowerSeriesEval_hasEval p n x hx
          (padicCompletedMultiplicativeUnitEndomorphism p u)
          (padicCompletedMultiplicativeUnitEndomorphism_hasSubst p u))
        (padicChangedUniformizerIntertwiner p u) := by
  let U := padicCompletedMultiplicativeUnitEndomorphism p u
  let Θ := padicChangedUniformizerIntertwiner p u
  have hseries :
      PowerSeries.map WittVector.frobenius Θ =
        PowerSeries.subst U Θ := by
    simpa only [U, Θ, padicCompletedMultiplicativeUnitEndomorphism] using
      (padicChangedUniformizerIntertwiner_frobenius p u)
  rw [hseries]
  exact
    padicCompletedLevelPowerSeriesEval_subst p n x hx U Θ
      (padicCompletedMultiplicativeUnitEndomorphism_hasSubst p u)
      (padicCompletedLevelPowerSeriesEval_hasEval p n x hx U
        (padicCompletedMultiplicativeUnitEndomorphism_hasSubst p u))

end LubinTate

end
