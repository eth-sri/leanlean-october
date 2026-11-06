module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.LocalField.NormUnits
public import ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Quotients
public import Mathlib.Data.Int.ModEq

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace LocalFieldTheory

/-!
# Field norm on unit groups

This file connects mathlib's `Algebra.norm` with the unit-group and valued-norm
APIs used by local CFT.
-/

noncomputable section

universe u v w

namespace DiscreteValuationField

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/-- The norm subgroup of `Kˣ` attached to `L/K`. -/
def fieldNormSubgroup : Subgroup Kˣ :=
  (normUnits K L).range

/-- The quotient map `Kˣ → Kˣ / N_{L/K}(Lˣ)` attached to the field norm. -/
def fieldNormQuotientMap :
    Kˣ →* Kˣ ⧸ fieldNormSubgroup K L :=
  QuotientGroup.mk' (fieldNormSubgroup K L)

/--
The defining evaluation formula for `fieldNormQuotientMap` is `fieldNormQuotientMap K L x =
QuotientGroup.mk' (fieldNormSubgroup K L) x`.
-/
@[simp] theorem fieldNormQuotientMap_apply (x : Kˣ) :
    fieldNormQuotientMap K L x =
      QuotientGroup.mk' (fieldNormSubgroup K L) x :=
  rfl

/-- Package a field norm as a `ValuedNorm` once the valuation formula has been
proved for the concrete extension.  The natural-number argument is not a
second source of extension-invariant data: `hformula` certifies it as the
valuation multiplier (and a source uniformizer makes that multiplier unique). -/
@[reducible] def valuedFieldNorm
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    ValuedNorm vK vL where
  toHom := normUnits K L
  residueDegree := residueDegree
  valuation_formula := hformula

/--
Establishes the identity `(valuedFieldNorm K L vK vL residueDegree hformula).toHom =
normUnits K L`.
-/
@[simp] theorem valuedFieldNorm_toHom
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    (valuedFieldNorm K L vK vL residueDegree hformula).toHom =
      normUnits K L :=
  rfl

/--
Establishes the identity `(valuedFieldNorm K L vK vL residueDegree hformula).normSubgroup =
fieldNormSubgroup K L`.
-/
theorem valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    (valuedFieldNorm K L vK vL residueDegree hformula).normSubgroup =
      fieldNormSubgroup K L := by
  rfl

/-- Concrete cyclic description of the field-norm quotient.  The assumptions
are the valuation formula for the field norm and the assertion that every
target valuation-zero element is already a field norm. -/
def fieldNormQuotientEquivZMod
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L) :
    Kˣ ⧸ fieldNormSubgroup K L ≃* Multiplicative (ZMod residueDegree) :=
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = fieldNormSubgroup K L := by
    simpa [N] using
      valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
        K L vK vL residueDegree hformula
  have hzero' : vK.zeroSubgroup ≤ N.normSubgroup := by
    rw [hnorm]
    exact hzero
  (QuotientGroup.quotientMulEquivOfEq hnorm.symm).trans
    (N.normQuotientEquivZMod hϖK hϖL hzero')
