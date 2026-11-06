module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The completed theta-intertwining theorem: the completed changed-uniformizer level

For `u ∈ κ⟦T⟧ˣ`, the theta construction used in the completed theta-intertwining theorem intertwines the
target parameter `T` with the source parameter `u⁻¹T`.  This file therefore
base-changes the primitive polynomial for `u⁻¹T` to the completed maximal-
unramified field, forms its genuine splitting field, and constructs the
primitive analytic evaluation point there.

The repository's primitive polynomial indexed by `n` cuts out division level
`n + 1`; this shift is kept explicit throughout.
-/

noncomputable section

open Filter
open scoped LaurentSeries NNReal Polynomial PowerSeries Topology WithZero

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

noncomputable local instance equalCharacteristicChangedCompletedBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

 instance equalCharacteristicChangedCompletedBaseCharP
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] :
    CharP (equalCharacteristicCompletedUnramifiedField F.residueField)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap F.residueField
      (equalCharacteristicCompletedUnramifiedField F.residueField)).injective
    F.residueCharacteristic
