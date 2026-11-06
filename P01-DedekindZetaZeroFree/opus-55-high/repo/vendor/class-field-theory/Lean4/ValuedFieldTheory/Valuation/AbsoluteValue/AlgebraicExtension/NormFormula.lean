module

public import ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness
public import ValuedFieldTheory.Valuation.AbsoluteValue.Completeness
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# the finite norm-formula theorem

Algebraic facts about the finite norm formula used in the explicit proof of
The algebraic-extension norm formula, together with restriction of a valued field tower to an
intermediate field.
-/


universe u v w x y z

namespace AlgebraicNumberTheory
namespace Valuations

theorem normFormula_real_natPow_rpow_inv_mul_cancel
    {a : ℝ} (ha : 0 ≤ a) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (a ^ n) ^ (1 / ((m * n : ℕ) : ℝ)) = a ^ (1 / (m : ℝ)) := by
  by_cases ha0 : a = 0
  · have hmn_ne : ((m * n : ℕ) : ℝ) ≠ 0 := by
      positivity
    simp_all
  · have ha_pos : 0 < a := by positivity
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha_pos.le]
    have hm_ne : (m : ℝ) ≠ 0 := by
      positivity
    have hn_ne : (n : ℝ) ≠ 0 := by
      positivity
    simp_all

/-- the finite norm-formula theorem, finite absolute-value norm-formula algebraic source: the
candidate `|N_{L/K}(x)|^(1/[L:K])` reduces to the same constant-term
formula as the spectral construction in the complete case.

This is purely algebraic and does not use Henselianity.  The remaining
the finite norm-formula theorem work is to identify the unique Henselian extension with this
candidate absolute value. -/
theorem normFormula_finiteExtensionNormFormulaValue_eq_minpoly_coeff_zero_rpow
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    finiteExtensionNormFormulaValue v x =
      v ((minpoly K x).coeff 0) ^
        (1 / ((minpoly K x).natDegree : ℝ)) := by
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  let : FiniteDimensional K (IntermediateField.adjoin K ({x} : Set L)) :=
    IntermediateField.adjoin.finiteDimensional hxint
  let : FiniteDimensional (IntermediateField.adjoin K ({x} : Set L)) L :=
    FiniteDimensional.right K (IntermediateField.adjoin K ({x} : Set L)) L
  have hd_pos : 0 < (minpoly K x).natDegree :=
    minpoly.natDegree_pos hxint
  have hr_pos :
      0 < Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L :=
    Module.finrank_pos
      (R := IntermediateField.adjoin K ({x} : Set L)) (M := L)
  have hnorm :
      v (Algebra.norm K x) =
        v ((minpoly K x).coeff 0) ^
          Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L := by
    rw [Algebra.norm_eq_norm_adjoin K x, map_pow]
    have hgen :
        Algebra.norm K (IntermediateField.AdjoinSimple.gen K x) =
          (-1 : K) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0 := by
      simpa [IntermediateField.adjoin.powerBasis_gen,
        IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim]
        using
          (Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
            (IntermediateField.adjoin.powerBasis hxint))
    simp_all
  rw [finiteExtensionNormFormulaValue, hnorm]
  rw [← Module.finrank_mul_finrank K
      (IntermediateField.adjoin K ({x} : Set L)) L,
    IntermediateField.adjoin.finrank hxint]
  exact normFormula_real_natPow_rpow_inv_mul_cancel
    (v.nonneg ((minpoly K x).coeff 0)) hd_pos hr_pos

/-- the finite norm-formula theorem, finite absolute-value norm-formula inverse source:
the norm-formula candidate sends inverses to inverses. -/
theorem normFormula_finiteExtensionNormFormulaValue_inv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    finiteExtensionNormFormulaValue v x⁻¹ =
      (finiteExtensionNormFormulaValue v x)⁻¹ := by
  rw [finiteExtensionNormFormulaValue, finiteExtensionNormFormulaValue,
    show Algebra.norm K x⁻¹ = (Algebra.norm K x)⁻¹ from
      Algebra.norm_inv (K := K) x,
    map_inv₀ v (Algebra.norm K x)]
  exact Real.inv_rpow (v.nonneg (Algebra.norm K x))
    (1 / (Module.finrank K L : ℝ))

/-- the finite norm-formula theorem, finite absolute-value norm-formula closed-unit/minpoly
source: the candidate is at most one exactly when the constant
coefficient of the minimal polynomial has base absolute value at most one. -/
theorem normFormula_finiteExtensionNormFormulaValue_le_one_iff_minpoly_coeff_zero_le_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    finiteExtensionNormFormulaValue v x ≤ 1 ↔
      v ((minpoly K x).coeff 0) ≤ 1 := by
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hd : 0 < (1 / ((minpoly K x).natDegree : ℝ)) := 
    one_div_pos.mpr (by
      exact_mod_cast (minpoly.natDegree_pos hxint))
  rw [normFormula_finiteExtensionNormFormulaValue_eq_minpoly_coeff_zero_rpow]
  simpa using
    (Real.rpow_le_rpow_iff
      (v.nonneg ((minpoly K x).coeff 0)) zero_le_one hd)

end Valuations
end AlgebraicNumberTheory

namespace DiscreteValuationField

namespace Valuation
