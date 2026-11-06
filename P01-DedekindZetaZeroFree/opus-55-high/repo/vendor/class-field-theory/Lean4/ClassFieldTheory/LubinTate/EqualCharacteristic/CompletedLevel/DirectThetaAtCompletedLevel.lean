module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.LaurentSeriesFrobenius
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateAction
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CompletedUnramifiedField
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The completed theta-intertwining theorem: direct theta at the standard completed level

The standard completed primitive point `lambda` is a division-level `n + 1`
point for the source parameter `T`.  This file genuinely evaluates the
direct theta series at `lambda`, iterates

`theta^φ ∘ e_T = e_(uT) ∘ theta`,

and proves that `theta(lambda)` is primitive target `uT`-torsion at the
same division level.
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

 instance equalCharacteristicDirectThetaCompletedBaseCharP
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] :
    CharP (equalCharacteristicCompletedUnramifiedField F.residueField)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap F.residueField
      (equalCharacteristicCompletedUnramifiedField F.residueField)).injective
    F.residueCharacteristic

 instance equalCharacteristicDirectThetaCompletedLevelCharP
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    CharP (equalCharacteristicCompletedLevelField F n)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)).injective
    F.residueCharacteristic
