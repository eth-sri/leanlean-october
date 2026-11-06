module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The equal-characteristic completed-unramified construction: finite unramified coefficient extensions in equal characteristic

For a finite extension `l / k` of finite fields, coefficientwise extension
makes `l((T))` a finite extension of `k((T))` of the same degree.  Every
automorphism of `l / k` extends coefficientwise, and these extensions exhaust
the Galois group of `l((T)) / k((T))`.  In particular, arithmetic Frobenius
on `l` gives the genuine Frobenius automorphism of this finite Laurent-series
base change and fixes `T`.

This is the finite unramified source used to model the completed maximal
unramified field in the equal-characteristic completed-unramified construction.  The construction is coefficientwise and does not
postulate an abstract unramified extension.
-/

noncomputable section

open scoped LaurentSeries PowerSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

variable {k : Type u} {l : Type v}

/-- The coefficientwise map `k((T)) -> l((T))` induced by a ring map
`k -> l`. -/
def laurentSeriesCoefficientMap
    {k : Type u} {l : Type v} [Field k] [Field l]
    (f : k →+* l) : k⸨X⸩ →+* l⸨X⸩ where
  toFun x := HahnSeries.map x f
  map_zero' := by
    change HahnSeries.map (0 : k⸨X⸩) f.toZeroHom = 0
    simp
  map_one' := by
    change HahnSeries.map (1 : k⸨X⸩) f.toMonoidWithZeroHom = 1
    simp
  map_add' x y := by
    change HahnSeries.map (x + y) f.toAddMonoidHom =
      HahnSeries.map x f.toAddMonoidHom + HahnSeries.map y f.toAddMonoidHom
    simp
  map_mul' x y := by
    change HahnSeries.map (x * y) f.toNonUnitalRingHom =
      HahnSeries.map x f.toNonUnitalRingHom * HahnSeries.map y f.toNonUnitalRingHom
    exact HahnSeries.map_mul (Γ := ℤ) f.toNonUnitalRingHom

/-- Mapping Laurent-series coefficients applies the ring homomorphism coefficientwise. -/
@[simp]
theorem laurentSeriesCoefficientMap_coeff
    [Field k] [Field l] (f : k →+* l) (x : k⸨X⸩) (m : ℤ) :
    (laurentSeriesCoefficientMap f x).coeff m = f (x.coeff m) :=
  rfl

/-- The induced `k((T))`-algebra structure on `l((T))`. -/
@[reducible]
def laurentSeriesCoefficientAlgebra
    [Field k] [Field l] [Algebra k l] : Algebra k⸨X⸩ l⸨X⸩ :=
  RingHom.toAlgebra
    (laurentSeriesCoefficientMap (algebraMap k l))

attribute [local instance] laurentSeriesCoefficientAlgebra


/-- A coefficient-field ring equivalence extends coefficientwise to Laurent
series. -/
def laurentSeriesCoefficientRingEquiv
    [Field k] [Field l] (e : k ≃+* l) : k⸨X⸩ ≃+* l⸨X⸩ where
  toFun := laurentSeriesCoefficientMap e.toRingHom
  invFun := laurentSeriesCoefficientMap e.symm.toRingHom
  left_inv x := by
    ext m
    simp
  right_inv x := by
    ext m
    simp
  map_add' := map_add (laurentSeriesCoefficientMap e.toRingHom)
  map_mul' := map_mul (laurentSeriesCoefficientMap e.toRingHom)

/-- A coefficientwise ring equivalence applies the base equivalence at every exponent. -/
@[simp]
theorem laurentSeriesCoefficientRingEquiv_coeff
    [Field k] [Field l] (e : k ≃+* l) (x : k⸨X⸩) (m : ℤ) :
    (laurentSeriesCoefficientRingEquiv e x).coeff m = e (x.coeff m) :=
  rfl

/-- An automorphism of the coefficient extension acts coefficientwise as an
automorphism over the Laurent-series base. -/
def laurentSeriesCoefficientAlgEquiv
    [Field k] [Field l] [Algebra k l]
    (e : l ≃ₐ[k] l) : l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩ := by
  letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  refine
    { laurentSeriesCoefficientRingEquiv e.toRingEquiv with
      commutes' := ?_ }
  intro x
  change laurentSeriesCoefficientMap e.toRingHom
      (laurentSeriesCoefficientMap (algebraMap k l) x) =
    laurentSeriesCoefficientMap (algebraMap k l) x
  ext m
  simp

/-- A coefficientwise algebra equivalence applies the base automorphism at every exponent. -/
@[simp]
theorem laurentSeriesCoefficientAlgEquiv_coeff
    [Field k] [Field l] [Algebra k l]
    (e : l ≃ₐ[k] l) (x : l⸨X⸩) (m : ℤ) :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    (laurentSeriesCoefficientAlgEquiv e x).coeff m = e (x.coeff m) :=
  rfl
