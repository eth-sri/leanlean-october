module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.InverseLimitCore
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.TopologyModelTypes
public import Mathlib.Tactic.NormNum

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

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
    norm_num
  map_add' x y := by
    norm_num

namespace DiscretePrincipalUnitQuotient

/-- Reduction between two wrapped discrete quotient coordinates. -/
def transition (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n) :
    DiscretePrincipalUnitQuotient F n →+
      DiscretePrincipalUnitQuotient F m where
  toFun x := of F m
    (Internal.principalUnitQuotientCarrierTransitionAdd F hmn x.val)
  map_zero' := by
    apply (addEquiv F m).injective
    change Internal.principalUnitQuotientCarrierTransitionAdd F hmn 0 = 0
    norm_num
  map_add' x y := by
    apply (addEquiv F m).injective
    change Internal.principalUnitQuotientCarrierTransitionAdd F hmn
        (x.val + y.val) =
      Internal.principalUnitQuotientCarrierTransitionAdd F hmn x.val +
        Internal.principalUnitQuotientCarrierTransitionAdd F hmn y.val
    norm_num

/-- The wrapped transition has the original additive transition as its value. -/
@[simp] theorem val_transition
    (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n)
    (x : DiscretePrincipalUnitQuotient F n) :
    (transition F hmn x).val =
      Internal.principalUnitQuotientCarrierTransitionAdd F hmn x.val :=
  rfl

end DiscretePrincipalUnitQuotient

end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

end
