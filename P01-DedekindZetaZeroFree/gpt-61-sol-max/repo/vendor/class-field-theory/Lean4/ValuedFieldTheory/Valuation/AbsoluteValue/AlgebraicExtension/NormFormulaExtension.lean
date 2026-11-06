module

public import Mathlib

public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# algebraic extension and integral closure

This file packages the explicit algebraic-extension statement.  A
valuation is represented by its valuation subring, so uniqueness is literal
equality of valuation subrings (equivalently, equivalence of valuations).
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

/-- the primitive factorization definition for the valuation subring attached to a nonarchimedean
absolute value, reduced to the exact factorization property used below. -/
theorem henselianValuation_iff_henselFactorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (absoluteValueValuationSubring
          v hnonarch).valuation ↔
      ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
        (absoluteValueValuationSubring v hnonarch) := by
  simp only [ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization,
    ValuationSubring.valuationSubring_valuation]

/-- the finite norm-formula theorem: a Henselian nonarchimedean valuation has exactly one
extension to every algebraic extension, and the valuation ring of that
extension is the actual integral closure of the base valuation ring.

The extension is expressed by its valuation subring.  The first conjunct says
that its canonical valuation extends the base valuation; the second is the
integral-closure identification. -/
theorem normFormula_algebraic_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring
        v hnonarch).valuation) :
    let V := absoluteValueValuationSubring v hnonarch
    ∃! W : ValuationSubring L,
      V.valuation.HasExtension W.valuation ∧
        W.toSubring = (integralClosure V L).toSubring := by
  let V := absoluteValueValuationSubring v hnonarch
  have hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty V :=
    (henselianValuation_iff_henselFactorization v hnonarch).1 hhens
  have hvalV :
      ∀ z : L,
        z ∈ (integralClosure V L).toSubring ∨
          z⁻¹ ∈ (integralClosure V L).toSubring :=
    normFormula_algebraic_integralClosure_mem_or_inv_of_henselFactorization
      v hnonarch hv
  have hval :
      ∀ z : L,
        z ∈ (integralClosure V.valuation.valuationSubring L).toSubring ∨
          z⁻¹ ∈
            (integralClosure V.valuation.valuationSubring L).toSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    exact hvalV
  let B  :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) V.valuation hval
  have hBext : V.valuation.HasExtension B.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) V.valuation hval
  have hBclosure : B.toSubring = (integralClosure V L).toSubring := by
    change
      (integralClosure V.valuation.valuationSubring L).toSubring =
        (integralClosure V L).toSubring
    rw [ValuationSubring.valuationSubring_valuation]
  refine ⟨B, ⟨hBext, hBclosure⟩, ?_⟩
  intro W hW
  let : V.valuation.HasExtension W.valuation := hW.1
  simpa only [ValuationSubring.valuationSubring_valuation] using
    DiscreteValuationField.Valuation.normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv
      (K := K) (L := L) V hval W.valuation

/-- Exact extension of nonarchimedean absolute values supplies extension of
the canonical valuations of their closed unit balls. -/
theorem absoluteValueValuation_hasExtension_of_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w)
    (hext : ∀ a : K, w (algebraMap K L a) = v a) :
    let V := absoluteValueValuationSubring v hv
    let W := absoluteValueValuationSubring w hw
    V.valuation.HasExtension W.valuation := by
  let V := absoluteValueValuationSubring v hv
  let W := absoluteValueValuationSubring w hw
  apply _root_.Valuation.HasExtension.ofComapInteger
  rw [ValuationSubring.integer_valuation, ValuationSubring.integer_valuation]
  have hcomap :=
    comap_absoluteValueUnitBallSubring_eq_of_extends
      v w hv hw hext
  assumption





























































































































































































end Valuations
end AlgebraicNumberTheory

end
