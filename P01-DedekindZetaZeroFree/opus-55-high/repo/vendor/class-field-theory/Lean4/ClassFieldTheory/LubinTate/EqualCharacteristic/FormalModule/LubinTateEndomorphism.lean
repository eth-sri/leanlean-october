module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Frobenius

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The equal-characteristic Lubin–Tate action: the equal-characteristic Lubin--Tate endomorphism

After identifying an equal-characteristic local field with `κ((T))`, the
Lubin--Tate polynomial used in the equal-characteristic construction is

`e(Y) = Y ^ q + T * Y`, where `q = #κ`.

This file constructs `e` as an actual additive endomorphism and constructs
the finite bracket

`[a]_<n> = ∑_{i<n} a_i e^i`, for `a = ∑ a_i T^i`.

Thus the unit action used below is the genuine Lubin--Tate action, not
ordinary scalar multiplication in the ambient field.
-/

noncomputable section

open scoped PowerSeries LaurentSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

 instance equalCharacteristicLaurentCharP
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] :
    CharP F.residueField⸨X⸩ F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap F.residueField F.residueField⸨X⸩).injective
    F.residueCharacteristic
