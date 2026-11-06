module

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

/-- A finite valued extension is unramified
when its residue extension is separable and its field degree equals its
residue degree. -/
def IsFiniteUnramified (base : DVF.{u, v} K) (target : DVF.{w, x} L)
    [base.valuation.HasExtension target.valuation] : Prop :=
  Algebra.IsSeparable base.residueField target.residueField ∧
    degree base target = residueDegree base target

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
    exact w.map_mul (x : L) (y : L)
  add_le_min x y := by
    exact w.add_le_min (x : L) (y : L)

@[simp]
theorem exponentialValuationRestrict_apply
    (w : LubinTate.Valuations.ExponentialValuation L) (E : IntermediateField K L) (x : E) :
    exponentialValuationRestrict w E x = w (x : L) :=
  rfl

/-- Exact extension is preserved when the target valuation is restricted to
an intermediate field. -/
theorem exponentialValuationRestrict_extends
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (E : IntermediateField K L) (a : K) :
    exponentialValuationRestrict w E (algebraMap K E a) = v a := by
  change w (algebraMap K L a) = v a
  exact hExt a

/-- The valuation-ring map associated with an exact extension of exponential
exponential valuations.  the fundamental inequality uses the same map internally; it is
exposed here because the finite unramified-extension definition also asks for separability of the actual
residue-field extension. -/
def unramifiedValuationRingValuationRingMap
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    LubinTate.Valuations.exponentialValuationSubring v →+*
      LubinTate.Valuations.exponentialValuationSubring w :=
  (algebraMap K L).restrict _ _ fun a ha ↦ by
    change (0 : WithTop ℝ) ≤ w (algebraMap K L a)
    rw [hExt]
    exact ha

@[simp]
theorem unramifiedValuationRingValuationRingMap_apply
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (a : LubinTate.Valuations.exponentialValuationSubring v) :
    ((unramifiedValuationRingValuationRingMap v w hExt a :
      LubinTate.Valuations.exponentialValuationSubring w) : L) =
        algebraMap K L (a : K) :=
  rfl

/-- Exact extension makes the finite unramified-extension valuation-ring map local, hence
it induces the actual map of residue fields used below. -/
theorem unramifiedValuationRingValuationRingMap_isLocalHom
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    IsLocalHom (unramifiedValuationRingValuationRingMap v w hExt) := by
  constructor
  intro a ha
  have hwzero :
      w (((unramifiedValuationRingValuationRingMap v w hExt) a :
        LubinTate.Valuations.exponentialValuationSubring w) : L) = 0 :=
    LubinTate.Valuations.exponentialValuation_eq_zero_of_isUnit w ha
  have hvzero : v (a : K) = 0 := by
    rw [unramifiedValuationRingValuationRingMap_apply, hExt] at hwzero
    exact hwzero
  exact LubinTate.Valuations.isUnit_of_exponentialValuation_eq_zero v hvzero

/-- Separability of the actual residue-field extension induced by an exact
extension of exponential valuations. -/
def ResidueExtensionIsSeparable
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) : Prop :=
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  letI : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  letI : Algebra V W := i.toAlgebra
  letI : Algebra (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) :=
    (IsLocalRing.ResidueField.map i).toAlgebra
  Algebra.IsSeparable (IsLocalRing.ResidueField V)
    (IsLocalRing.ResidueField W)

/-- Literal finite-extension form for the
general exponential valuations.

The first conjunct is separability of the *actual residue-field extension*.
The second is exactly `[L : K] = [lambda : kappa]`, with the right-hand side
given by the actual residue finrank from the fundamental inequality.  In particular no
separability assumption on the field extension `L/K` is inserted. -/
def FiniteUnramifiedExtension
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) : Prop :=
  ResidueExtensionIsSeparable v w hExt ∧
    Module.finrank K L = exponentialResidueDegree v w hExt

/-- Projection of residue separability in the literal finite the finite unramified-extension definition
predicate. -/
theorem finiteUnramifiedExtension_residue_isSeparable
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (h : FiniteUnramifiedExtension v w hExt) :
    ResidueExtensionIsSeparable v w hExt :=
  h.1

/-- Projection of the degree equality in the literal finite the finite unramified-extension definition
predicate. -/
theorem finiteUnramifiedExtension_degree_eq_residueDegree
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (h : FiniteUnramifiedExtension v w hExt) :
    Module.finrank K L = exponentialResidueDegree v w hExt := by
  exact h.2

/-- A finite intermediate extension is unramified when its restricted
valuation satisfies the literal finite condition of the finite unramified-extension definition. -/
def FiniteUnramifiedSubextension
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (E : IntermediateField K L) : Prop :=
  ∃ hfin : FiniteDimensional K E,
    letI : FiniteDimensional K E := hfin
    FiniteUnramifiedExtension v
      (exponentialValuationRestrict w E)
      (exponentialValuationRestrict_extends v w hExt E)













end UnramifiedExtensions

end Valuations
end AlgebraicNumberTheory

end
