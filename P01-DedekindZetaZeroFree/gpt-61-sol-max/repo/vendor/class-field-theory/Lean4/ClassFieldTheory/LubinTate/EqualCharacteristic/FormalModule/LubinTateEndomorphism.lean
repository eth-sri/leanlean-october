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






set_option autoImplicit false

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





























































/-- Multiplication by a residue-field coefficient, regarded as an additive
endomorphism of the Laurent-series field. -/
noncomputable def equalCharacteristicCoefficientEnd
    (F : LocalField.{u, v} K) (a : F.residueField) :
    AddMonoid.End F.residueField⸨X⸩ where
  toFun x :=
    algebraMap F.residueField F.residueField⸨X⸩ a * x
  map_zero' := mul_zero _
  map_add' := mul_add _

/-- A residue coefficient endomorphism acts by scalar multiplication. -/
@[simp]
theorem equalCharacteristicCoefficientEnd_apply
    (F : LocalField.{u, v} K) (a : F.residueField)
    (x : F.residueField⸨X⸩) :
    equalCharacteristicCoefficientEnd F a x =
      algebraMap F.residueField F.residueField⸨X⸩ a * x :=
  rfl






















































































































































































end EqualCharacteristic
end LubinTate

end
