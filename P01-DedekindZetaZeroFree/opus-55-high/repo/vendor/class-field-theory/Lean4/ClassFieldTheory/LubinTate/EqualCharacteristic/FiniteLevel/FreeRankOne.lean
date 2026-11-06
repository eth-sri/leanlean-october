module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.FreeModule.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The primitive-division-module equivalence: equal-characteristic division points are free of rank one

For the standard equal-characteristic Lubin--Tate series, the points killed by
the `(n + 1)`-st iterate form a free rank-one module over
`κ⟦T⟧/(T^(n+1))`.  The shift is intentional: the existing division-tower
The primitive polynomial is indexed by `n`, while its roots lie at division
level `n + 1`.
-/

noncomputable section

open scoped PowerSeries LaurentSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- All coefficients visible at division level `n + 1`.  In contrast with the
unit parameters used for the primitive roots in the uniformizer norm identity, the constant
coefficient is allowed to vanish; this is necessary to parametrize every
division point. -/
structure equalCharacteristicLubinTateParameter
    (F : LocalField.{u, v} K) (n : ℕ) where
  /-- The coefficients in degrees `0` through `n` of the represented truncated series. -/
  coeff : Fin (n + 1) → F.residueField

/-- A Lubin–Tate parameter evaluates to its finite coefficient function. -/
instance equalCharacteristicLubinTateParameter_coeFun
    (F : LocalField.{u, v} K) (n : ℕ) :
    CoeFun (equalCharacteristicLubinTateParameter F n)
      (fun _ => Fin (n + 1) → F.residueField) :=
  ⟨equalCharacteristicLubinTateParameter.coeff⟩

/-- The canonical polynomial representative of a finite parameter. -/
def equalCharacteristicLubinTateParameterSeries
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : equalCharacteristicLubinTateParameter F n) :
    F.residueField⟦X⟧ :=
  PowerSeries.mk fun i =>
    if hi : i < n + 1 then a ⟨i, hi⟩ else 0

/-- The coefficient ring at division level `n + 1`. -/
def equalCharacteristicLubinTateTruncatedRing
    (F : LocalField.{u, v} K) (n : ℕ) :=
  F.residueField⟦X⟧ ⧸
    Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧)

/-- The commutative ring structure on the named truncated coefficient
ring. -/
instance equalCharacteristicLubinTateTruncatedRing_commRing
    (F : LocalField.{u, v} K) (n : ℕ) :
    CommRing (equalCharacteristicLubinTateTruncatedRing F n) := by
  change CommRing
    (F.residueField⟦X⟧ ⧸
      Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧))
  infer_instance

/-- The canonical scalar multiplication of the truncated coefficient ring on
itself, named to prevent typeclass search from unfolding the quotient. -/
noncomputable local instance equalCharacteristicLubinTateTruncatedSelfSMul
    (F : LocalField.{u, v} K) (n : ℕ) :
    SMul (equalCharacteristicLubinTateTruncatedRing F n)
      (equalCharacteristicLubinTateTruncatedRing F n) where
  smul := (· * ·)

noncomputable local instance equalCharacteristicLubinTateTruncatedSelfModule
    (F : LocalField.{u, v} K) (n : ℕ) :
    Module (equalCharacteristicLubinTateTruncatedRing F n)
      (equalCharacteristicLubinTateTruncatedRing F n) :=
  Semiring.toModule
