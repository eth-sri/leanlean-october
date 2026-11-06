module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.InverseLimitCore
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.TopologyModelTypes

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Transitions between principal-unit quotients

These additive maps use the concrete principal-unit filtration of a complete
discrete valuation field. Neither finiteness nor a scalar action is required.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

open ValuationTheory.DiscreteValuationField
open Internal

universe u v

variable {K : Type u} [Field K]

/-- Additive form of a transition between principal-unit quotients. -/
def Internal.principalUnitQuotientCarrierTransitionAdd
    (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n) :
    Additive (Internal.principalUnitQuotientCarrier F n) →+
      Additive (Internal.principalUnitQuotientCarrier F m) where
  toFun x := Additive.ofMul
    (principalUnitQuotientCarrierTransition F hmn (Additive.toMul x))
  map_zero' := by
    rfl
  map_add' x y := by
    simp

namespace DiscretePrincipalUnitQuotient
