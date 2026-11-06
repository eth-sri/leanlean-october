module

public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
public import ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialBounds
public import ValuedFieldTheory.Valuation.UniqueRing
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import ValuedFieldTheory.Valuation.Henselian.Factorization.CoefficientMinimum
public import ValuedFieldTheory.Valuation.Henselian.Core
public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# unique extension criterion

Valuations are regarded valuations up to equivalence.  Accordingly, uniqueness on
an algebraic extension is stated as literal uniqueness of its valuation
subring.  This is the same endpoint used in the finite norm-formula theorem.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

universe u

/-- A valuation subring has a unique extension valuation ring to `L`. -/
def HasUniqueValuationSubringExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) : Prop :=
  ∃! W : ValuationSubring L, V.valuation.HasExtension W.valuation

/-- the unique-extension criterion, forward direction.  the primitive factorization definition, in its exact
factorization form, gives a unique extension valuation ring on every
algebraic extension. -/
theorem henselianUniqueExtension_unique_algebraic_valuationSubring_extension_of_henselian
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring
        v hnonarch).valuation) :
    HasUniqueValuationSubringExtension
      (L := L) (absoluteValueValuationSubring v hnonarch) := by
  let V := absoluteValueValuationSubring v hnonarch
  obtain ⟨B, hB, hBuniq⟩ :=
    normFormula_algebraic_extension (K := K) (L := L)
      v hnonarch hhens
  refine ⟨B, hB.1, ?_⟩
  intro W hW
  apply hBuniq W
  refine ⟨hW, ?_⟩
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
  let : V.valuation.HasExtension W.valuation := hW
  have hWic :
      W =
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) V.valuation hval := by
    simpa only [ValuationSubring.valuationSubring_valuation] using
      DiscreteValuationField.Valuation.normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv
        (K := K) (L := L) V hval W.valuation
  change W.toSubring = (integralClosure V L).toSubring
  rw [hWic]
  ext z
  change z ∈
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) V.valuation hval ↔ z ∈ (integralClosure V L).toSubring
  rw [ValuationTheory.DiscreteValuationField.Valuation.mem_integralClosureValuationSubringOfMemOrInv
      V.valuation hval z]
  rw [ValuationSubring.valuationSubring_valuation]
