module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
public import Mathlib.FieldTheory.Galois.Abelian

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The uniformizer norm identity: abelian equal-characteristic Lubin--Tate level fields

The finite unit parameters constructed previously exhaust the automorphisms
of a level field.  To prove commutativity genuinely, we express each truncated
bracket as evaluation of a polynomial over the Laurent-series base.  Algebra
maps therefore commute with brackets.  Multiplicativity of the genuine
truncated brackets on division points and commutativity of power-series
multiplication then show that any two parameter automorphisms commute on the
power-basis generator, hence everywhere.
-/


open scoped PowerSeries LaurentSeries Polynomial

universe u v w

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The power-basis generator is the chosen primitive point in the ambient
separable closure. -/
@[simp]
theorem equalCharacteristicLubinTateLevelPowerBasis_gen_coe
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    ((equalCharacteristicLubinTateLevelPowerBasis F n).gen :
      SeparableClosure F.residueField⸨X⸩) =
        chosenEqualCharacteristicLubinTatePrimitiveRoot F n :=
  rfl
