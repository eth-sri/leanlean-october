module

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
  simp [ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization, ValuationSubring.valuationSubring_valuation]

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- the finite norm-formula theorem: a Henselian nonarchimedean valuation has exactly one
extension to every algebraic extension, and the valuation ring of that
extension is the actual integral closure of the base valuation ring.

The extension is expressed by its valuation subring.  The first conjunct says
that its canonical valuation extends the base valuation; the second is the
integral-closure identification. -/
theorem normFormula_algebraic_extension
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
  have hval :
      ∀ z : L,
        z ∈ (integralClosure V.valuation.valuationSubring L).toSubring ∨
          z⁻¹ ∈
            (integralClosure V.valuation.valuationSubring L).toSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    exact (normFormula_algebraic_integralClosure_mem_or_inv_of_henselFactorization
      v hnonarch ((henselianValuation_iff_henselFactorization v hnonarch).1 hhens))
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
       V.valuation hval
  have hBclosure : B.toSubring = (integralClosure V L).toSubring := by
    change
      (integralClosure V.valuation.valuationSubring L).toSubring =
        (integralClosure V L).toSubring
    rw [ValuationSubring.valuationSubring_valuation]
  refine ⟨B, ⟨(ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_hasExtension
    V.valuation hval), hBclosure⟩, ?_⟩
  intro W hW
  let := hW.1
  simpa using
    DiscreteValuationField.Valuation.normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv
        V hval W.valuation

/-- Exact extension of nonarchimedean absolute values supplies extension of
the canonical valuations of their closed unit balls. -/
theorem absoluteValueValuation_hasExtension_of_extends
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
  simp [ValuationSubring.integer_valuation]
  apply comap_absoluteValueUnitBallSubring_eq_of_extends <;> assumption

end Valuations
end AlgebraicNumberTheory

end
