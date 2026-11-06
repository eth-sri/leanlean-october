module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.LaurentSeriesFrobenius
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateAction
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaAtCompletedLevel
public import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The completed theta-intertwining theorem: the formal standard bracket at a completed division point

The first theta identity uses the independently constructed formal bracket,
whereas the completed Frobenius lift acts through the finite bracket from
the finite Lubin–Tate bracket construction.  This file proves that the two actions agree on the chosen primitive
division point.  The proof analytically evaluates the recursive identity

`[a](x) = a₀x + [tail(a)](e_T(x))`

and follows the source torsion orbit until the finite bracket terminates.
-/

noncomputable section

open Filter
open scoped LaurentSeries NNReal NormedField PowerSeries
  PowerSeries.WithPiTopology Topology Valued WithZero

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

 instance equalCharacteristicDirectBracketLevelCharP
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    CharP (equalCharacteristicCompletedLevelField F n)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)).injective
    F.residueCharacteristic
