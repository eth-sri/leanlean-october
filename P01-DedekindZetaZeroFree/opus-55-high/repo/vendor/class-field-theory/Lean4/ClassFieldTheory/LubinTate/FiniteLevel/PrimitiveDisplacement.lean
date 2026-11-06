module

public import ClassFieldTheory.LubinTate.FiniteLevel.CompletedIterates
public import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveAction
public import ClassFieldTheory.LubinTate.FiniteLevel.LevelAutomorphisms
public import ValuedFieldTheory.Ramification.HilbertRamification.CompleteDVF
public import ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Inverse

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Displacements of primitive Lubin--Tate points

For the primitive point at level `n + 1`, a unit whose first nontrivial
principal-unit layer is `k` displaces that point by an element of normalized
additive valuation `q ^ k`.

The analytic input is proved here rather than assumed.  A unit scalar
endomorphism is `X` times an invertible power series.  Likewise
`F(X, Y) - X` for the standard formal group is `Y` times an invertible
two-variable power series.  Consequently neither operation changes the
valuation of the topologically nilpotent input that it multiplies.
-/

noncomputable section

open scoped Polynomial PowerSeries

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF

open ValuationTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

section FormalFactors

theorem coeff_subst_X_zero
    {R : Type*} [CommRing R]
    (f : MvPowerSeries (Fin 2) R) (d : Fin 2 →₀ ℕ)
    (hd : d 1 = 0) :
    PowerSeries.coeff (d 0)
        (MvPowerSeries.subst
          ![(PowerSeries.X : PowerSeries R), 0] f) =
      MvPowerSeries.coeff d f := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst,
    finsum_eq_single _ d]
  · simp [hd, PowerSeries.coeff_X_pow]
  · intro e hed
    by_cases he : e 1 = 0
    · have he0 : e 0 ≠ d 0 := by
        intro he0
        apply hed
        ext i
        fin_cases i
        · exact he0
        · exact he.trans hd.symm
      simp [he, PowerSeries.coeff_X_pow, he0.symm]
    · simp [he]
  · exact MvPowerSeries.HasSubst.X_zero

/-- The standard formal-group difference `F(X,Y) - X` is divisible by
`Y`. -/
 theorem standardLubinTateFormalGroup_rightDisplacement_dvd
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    (MvPowerSeries.X (1 : Fin 2) :
        MvPowerSeries (Fin 2) F.valuationSubring) ∣
      SameUniformizer.standardFormalGroupPowerSeries hπ -
        MvPowerSeries.X (0 : Fin 2) := by
  rw [MvPowerSeries.X_dvd_iff]
  intro d hd
  let D :=
    SameUniformizer.standardFormalGroupPowerSeries hπ -
      MvPowerSeries.X (0 : Fin 2)
  have hhas :
      MvPowerSeries.HasSubst
        (![(PowerSeries.X : PowerSeries F.valuationSubring), 0] :
          Fin 2 → PowerSeries F.valuationSubring) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i
    · simpa only [Fin.zero_eta, Matrix.cons_val_zero,
        PowerSeries.X_apply] using
        (MvPowerSeries.constantCoeff_X
          (R := F.valuationSubring) ())
    · simp
  have hsubst :
      MvPowerSeries.subst
          ![(PowerSeries.X : PowerSeries F.valuationSubring), 0] D =
        0 := by
    dsimp only [D]
    rw [MvPowerSeries.subst_sub hhas]
    have hformal :
        MvPowerSeries.subst
            ![(PowerSeries.X : PowerSeries F.valuationSubring), 0]
            (SameUniformizer.standardFormalGroupPowerSeries hπ) =
          PowerSeries.X := by
      simpa only [PowerSeries.X_apply] using
        SameUniformizer.standardFormalGroupPowerSeries_subst_X_zero hπ
    rw [hformal, MvPowerSeries.subst_X hhas]
    exact sub_self _
  have hcoeff :=
    congrArg (PowerSeries.coeff (d 0)) hsubst
  rw [coeff_subst_X_zero D d hd] at hcoeff
  simpa [D] using hcoeff

/-- The quotient of `F(X,Y) - X` by `Y`. -/
 def standardLubinTateFormalGroupRightDisplacementFactor
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    MvPowerSeries (Fin 2) F.valuationSubring :=
  Classical.choose
    (standardLubinTateFormalGroup_rightDisplacement_dvd hπ)

end FormalFactors

section AnalyticValuation

 noncomputable local instance
    standardLubinTatePrimitiveDisplacementCoefficientUniformSpace :
    UniformSpace F.valuationSubring :=
  ⊥

 noncomputable local instance
    standardLubinTatePrimitiveDisplacementTargetWithIdeal
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    WithIdeal
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring where
  i := (standardLubinTateLevelCompleteDVF hπ n).maximalIdeal

 noncomputable local instance
    standardLubinTatePrimitiveDisplacementTargetCompleteSpace
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    CompleteSpace
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

 noncomputable local instance
    standardLubinTatePrimitiveDisplacementTargetT2Space
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    T2Space
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

 noncomputable local instance
    standardLubinTatePrimitiveDisplacementAlgebra
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Algebra F.valuationSubring
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  (standardLubinTateLevelCoefficientHom hπ n).toAlgebra

/-- The analytic value of `[π^k]` is the evaluated standard polynomial
iterate. -/
theorem standardLubinTateEndomorphismValue_uniformizer_pow
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) :
    standardLubinTateEndomorphismValue hπ n (π ^ k) =
      standardLubinTatePrimitivePointIterateInteger hπ n k := by
  exact
    standardLubinTateEndomorphismEvalAt_uniformizer_pow hπ n
      (standardLubinTatePrimitivePointInteger hπ n)
      (standardLubinTatePrimitivePointInteger_hasEval hπ n) k

/-- Every evaluated standard iterate before the annihilating level is
topologically nilpotent. -/
theorem standardLubinTatePrimitivePointIterateInteger_hasEval
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) :
    PowerSeries.HasEval
      (standardLubinTatePrimitivePointIterateInteger hπ n k) := by
  rw [← standardLubinTateEndomorphismValue_uniformizer_pow hπ n k]
  exact standardLubinTateEndomorphismValue_hasEval hπ n (π ^ k)
