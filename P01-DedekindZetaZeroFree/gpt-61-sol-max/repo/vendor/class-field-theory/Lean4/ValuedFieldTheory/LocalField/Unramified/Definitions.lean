module

public import Mathlib

public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Finite and algebraic unramified valued extensions

Finite unramified valued extensions are expressed directly by the
degree equality and residue separability condition.
-/

noncomputable section

universe u v w x

open ValuationTheory.DiscreteValuationField

namespace ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]









end ValuationTheory.DiscreteValuationField.ValuedExtension

namespace ValuationTheory.DiscreteValuationField.ValuedExtension

section AlgebraicUnramified

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (ambient : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension ambient.valuation]

























/- the finite unramified-extension definition finite-support eliminator.

In an algebraic unramified ambient extension, every finitely generated
intermediate field is contained in a finite unramified subextension. -/













end AlgebraicUnramified

end ValuationTheory.DiscreteValuationField.ValuedExtension

namespace AlgebraicNumberTheory
namespace Valuations

section UnramifiedExtensions

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- Restriction of an exponential valuation to an intermediate field.
This is the valuation carried by each finite subextension in the union clause
of the finite unramified-extension definition. -/
def exponentialValuationRestrict
    (w : LubinTate.Valuations.ExponentialValuation L) (E : IntermediateField K L) :
    LubinTate.Valuations.ExponentialValuation E where
  toFun x := w (x : L)
  eq_top_iff x := by
    rw [w.eq_top_iff]
    simp
  map_mul x y := by
    apply w.map_mul
  add_le_min x y := by
    apply w.add_le_min

@[simp]
theorem exponentialValuationRestrict_apply
    (w : LubinTate.Valuations.ExponentialValuation L) (E : IntermediateField K L) (x : E) :
    exponentialValuationRestrict w E x = w (x : L) :=
  rfl

















































































































































































end UnramifiedExtensions

end Valuations
end AlgebraicNumberTheory

end
