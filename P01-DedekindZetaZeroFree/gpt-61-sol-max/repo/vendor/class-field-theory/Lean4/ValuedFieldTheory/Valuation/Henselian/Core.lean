module

public import Mathlib

public import ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite
public import ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianValuationExtension
public import ValuedFieldTheory.Valuation.HenselLemma
public import ValuedFieldTheory.Valuation.Henselian.Factorization.AdicLimits
public import ValuedFieldTheory.Valuation.Henselian.Factorization.Assembly
public import ValuedFieldTheory.Valuation.Henselian.Factorization.Basic
public import ValuedFieldTheory.Valuation.Henselian.Factorization.CoefficientMinimum
public import ValuedFieldTheory.Valuation.Henselian.Factorization.Complete
public import ValuedFieldTheory.Valuation.Henselian.Factorization.DegreeBounds
public import ValuedFieldTheory.Valuation.Henselian.Factorization.DivisionBounds
public import ValuedFieldTheory.Valuation.Henselian.Factorization.ErrorPowers
public import ValuedFieldTheory.Valuation.Henselian.Factorization.FiniteApproximation
public import ValuedFieldTheory.Valuation.Henselian.Factorization.InfiniteApproximation
public import ValuedFieldTheory.Valuation.Henselian.Factorization.Iteration
public import ValuedFieldTheory.Valuation.Henselian.Factorization.PrincipalLimits
public import ValuedFieldTheory.Valuation.Henselian.Factorization.Step
public import ValuedFieldTheory.Valuation.Henselian.Factorization.Truncation
public import ValuedFieldTheory.Valuation.Henselian.Factorization.WeakLimits
public import ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialLifting
public import ValuedFieldTheory.Valuation.Henselian.UniqueExtensionReduction

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






















set_option autoImplicit false

namespace ValuationTheory

/-!
# Henselian discretely valued fields

The Henselian factorization condition and the residual linear-factor lemmas used in the
residual linear-factor criterion.
-/

noncomputable section

namespace DiscreteValuationField

universe u v

/-- The factorization form of Hensel's lemma used in the Henselian factorization condition.

Every primitive polynomial whose reduction is a product of coprime factors has
degree-controlled lifts with the prescribed reductions. -/
def HenselFactorizationProperty {K : Type u} [Field K]
    (V : ValuationSubring K)  :=
  ∀ {f : Polynomial V}
      {gbar hbar : Polynomial (IsLocalRing.ResidueField V)},
    f.map (IsLocalRing.residue V) ≠ 0 →
      f.map (IsLocalRing.residue V) = gbar * hbar →
        IsCoprime gbar hbar →
          ∃ G H : Polynomial V,
            G.natDegree = gbar.natDegree ∧
              H.natDegree ≤ f.natDegree - gbar.natDegree ∧
                f = G * H ∧
                  G.map (IsLocalRing.residue V) = gbar ∧
                    H.map (IsLocalRing.residue V) = hbar

/-- The Henselian factorization condition: a valuation is Henselian when its valuation ring
satisfies Hensel's lemma in the factorization sense. -/
def HenselianValuationByFactorization {K : Type u} [Field K]
    {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]
    (val : _root_.Valuation K Γ)  :=
  HenselFactorizationProperty val.valuationSubring




















































































end DiscreteValuationField

end

end ValuationTheory
