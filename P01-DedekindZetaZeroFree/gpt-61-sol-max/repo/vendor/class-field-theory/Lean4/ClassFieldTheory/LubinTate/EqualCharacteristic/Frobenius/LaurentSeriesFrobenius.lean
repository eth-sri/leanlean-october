module

public import Mathlib

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.LocalField.DiscreteValuationField.FiniteCoefficientLaurent
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

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
noncomputable def laurentSeriesCoefficientMap
    {k : Type u} {l : Type v} [Field k] [Field l]
    (f : k →+* l) : k⸨X⸩ →+* l⸨X⸩ where
  toFun x := HahnSeries.map x f
  map_zero' := by
    change HahnSeries.map (0 : k⸨X⸩) f.toZeroHom = 0
    apply HahnSeries.map_zero
  map_one' := by
    change HahnSeries.map (1 : k⸨X⸩) f.toMonoidWithZeroHom = 1
    apply HahnSeries.map_one
  map_add' x y := by
    change HahnSeries.map (x + y) f.toAddMonoidHom =
      HahnSeries.map x f.toAddMonoidHom + HahnSeries.map y f.toAddMonoidHom
    apply HahnSeries.map_add
  map_mul' x y := by
    change HahnSeries.map (x * y) f.toNonUnitalRingHom =
      HahnSeries.map x f.toNonUnitalRingHom * HahnSeries.map y f.toNonUnitalRingHom
    apply HahnSeries.map_mul

/-- Mapping Laurent-series coefficients applies the ring homomorphism coefficientwise. -/
@[simp]
theorem laurentSeriesCoefficientMap_coeff
    [Field k] [Field l] (f : k →+* l) (x : k⸨X⸩) (m : ℤ) :
    (laurentSeriesCoefficientMap f x).coeff m = f (x.coeff m) :=
  rfl

/-- The coefficient map sends a constant series to the mapped constant series. -/
@[simp]
theorem laurentSeriesCoefficientMap_C
    [Field k] [Field l] (f : k →+* l) (a : k) :
    laurentSeriesCoefficientMap f (HahnSeries.C (Γ := ℤ) a) =
      HahnSeries.C (Γ := ℤ) (f a) := by
  change HahnSeries.map (HahnSeries.C (Γ := ℤ) a) f = _
  exact HahnSeries.map_C a f













/-- The induced `k((T))`-algebra structure on `l((T))`. -/
@[reducible]
noncomputable def laurentSeriesCoefficientAlgebra
    [Field k] [Field l] [Algebra k l] : Algebra k⸨X⸩ l⸨X⸩ :=
  RingHom.toAlgebra
    (laurentSeriesCoefficientMap (algebraMap k l))









attribute [local instance] laurentSeriesCoefficientAlgebra



























section FiniteBasis

variable [Field k] [Field l] [Algebra k l]
  {ι : Type*} [Fintype ι]


















































































end FiniteBasis























section
variable [Field k] [Field l]
/-- A coefficient-field ring equivalence extends coefficientwise to Laurent
series. -/
noncomputable def laurentSeriesCoefficientRingEquiv
      (e : k ≃+* l) : k⸨X⸩ ≃+* l⸨X⸩ where
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
      (e : k ≃+* l) (x : k⸨X⸩) (m : ℤ) :
    (laurentSeriesCoefficientRingEquiv e x).coeff m = e (x.coeff m) :=
  rfl

/-- An automorphism of the coefficient extension acts coefficientwise as an
automorphism over the Laurent-series base. -/
noncomputable def laurentSeriesCoefficientAlgEquiv
      [Algebra k l]
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
  change e (algebraMap k l (x.coeff m)) = algebraMap k l (x.coeff m)
  apply e.commutes

/-- A coefficientwise algebra equivalence applies the base automorphism at every exponent. -/
@[simp]
theorem laurentSeriesCoefficientAlgEquiv_coeff
      [Algebra k l]
    (e : l ≃ₐ[k] l) (x : l⸨X⸩) (m : ℤ) :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    (laurentSeriesCoefficientAlgEquiv e x).coeff m = e (x.coeff m) :=
  rfl















/-- Coefficientwise extension as a homomorphism between the two Galois
groups. -/
noncomputable def laurentSeriesCoefficientGalHom
      [Algebra k l] :
    (l ≃ₐ[k] l) →* (l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩) := by
  letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  exact
    { toFun := laurentSeriesCoefficientAlgEquiv
      map_one' := by
        apply AlgEquiv.ext
        intro x
        ext m
        simp
      map_mul' := by
        intro e f
        apply AlgEquiv.ext
        intro x
        ext m
        simp }

/-- The Galois homomorphism sends an automorphism to its coefficientwise Laurent action. -/
@[simp]
theorem laurentSeriesCoefficientGalHom_apply
      [Algebra k l]
    (e : l ≃ₐ[k] l) :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    laurentSeriesCoefficientGalHom e = laurentSeriesCoefficientAlgEquiv e :=
  rfl
end











section FiniteFields

variable [Field k] [Finite k] [Field l] [Finite l] [Algebra k l]





















































































end FiniteFields

section ChosenFiniteExtension

variable (k : Type u) [Field k] [Finite k]
  (p n : ℕ) [Fact p.Prime] [CharP k p] [NeZero n]

/-- The finite unramified Laurent-series extension obtained from the chosen
degree-`n` extension of the residue field. -/
def equalCharacteristicFiniteUnramifiedExtension :=
  (FiniteField.Extension k p n)⸨X⸩

/-- The finite unramified Laurent-series extension is a field. -/
instance equalCharacteristicFiniteUnramifiedExtension_field :
    Field (equalCharacteristicFiniteUnramifiedExtension k p n) := by
  change Field ((FiniteField.Extension k p n)⸨X⸩)
  infer_instance

/-- The finite unramified extension is an algebra over the base Laurent field. -/
noncomputable instance equalCharacteristicFiniteUnramifiedAlgebra :
    Algebra k⸨X⸩ (equalCharacteristicFiniteUnramifiedExtension k p n) :=
  laurentSeriesCoefficientAlgebra

section

local instance equalCharacteristicFiniteUnramifiedModule :
    @Module k⸨X⸩ (equalCharacteristicFiniteUnramifiedExtension k p n)
      (inferInstance : DivisionRing k⸨X⸩).toRing.toSemiring
      (inferInstance : AddCommGroup
        (equalCharacteristicFiniteUnramifiedExtension k p n)).toAddCommMonoid :=
  @Algebra.toModule k⸨X⸩ (equalCharacteristicFiniteUnramifiedExtension k p n)
    _ _ (equalCharacteristicFiniteUnramifiedAlgebra k p n)







end


























































































end ChosenFiniteExtension

end EqualCharacteristic
end LubinTate

end
