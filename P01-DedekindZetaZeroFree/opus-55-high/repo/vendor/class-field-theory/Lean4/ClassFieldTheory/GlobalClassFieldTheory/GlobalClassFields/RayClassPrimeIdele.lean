module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldPrimeSplitting
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealArtinQuotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Prime idèles and ideal ray classes

A normalized one-place prime idèle is prime to every modulus whose
finite support omits that prime.  Its fractional ideal is the
corresponding prime ideal, so the idelic and ideal-theoretic ray-class
constructions use exactly the same prime representative.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

universe u

theorem rayClassPrimeIdeleClassGroupIsMulCommutative
    (F : Type u) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) := by apply instIsMulCommutativeIdeleClassGroup <;> assumption

attribute [local instance] rayClassPrimeIdeleClassGroupIsMulCommutative

section GenericPrimeIdele

variable {K : Type u} [Field K] [NumberField K]

/-- A normalized one-place prime idèle is prime to a modulus whenever
the supporting prime does not occur in the modulus. -/
theorem finitePrimeIdele_mem_idelePrimeToModulusSubgroup
    (m : RayClass.Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    finitePrimeIdele v ∈
      RayClass.idelePrimeToModulusSubgroup m := by
  constructor
  · change
      1 ∈
        m.infiniteCongruenceSubgroup
    exact
      m.infiniteCongruenceSubgroup.one_mem
  · intro w hw
    have hwv : w ≠ v := by
      intro h
      exact hv (h ▸ hw)
    change
      IdeleGroup.finiteComponent w
          (finitePrimeIdele v) ∈
        RayClass.localHigherUnitGroup w (m.finitePart w)
    rw [finitePrimeIdele,
      IdeleGroup.finitePlaceIdele_finiteComponent_of_ne
        v w (FiniteIdeleGroup.chosenLocalOrderSection v 1) hwv]
    simp

/-- The fractional-ideal image of a normalized one-place prime idèle,
viewed as prime to a modulus, is the corresponding prime-to-modulus
prime ideal. -/
@[simp]
theorem primeToIdealMap_finitePrimeIdele
    (m : RayClass.Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    RayClass.primeToIdealMap m
        ⟨finitePrimeIdele v,
          finitePrimeIdele_mem_idelePrimeToModulusSubgroup
            m v hv⟩ =
      RayClass.primeToModulusIdeal m v hv := by
  apply Subtype.ext
  exact
    fractionalIdeal_finitePrimeIdele v

/-- The ideal-ray projection of a normalized one-place prime idèle is
the ideal ray class of the corresponding prime ideal. -/
@[simp]
theorem idealRayProjection_finitePrimeIdele
    (m : RayClass.Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    RayClass.idealRayProjection m
        ⟨finitePrimeIdele v,
          finitePrimeIdele_mem_idelePrimeToModulusSubgroup
            m v hv⟩ =
      QuotientGroup.mk'
        (RayClass.principalRayIdealSubgroup m)
        (RayClass.primeToModulusIdeal m v hv) := by
  rw [RayClass.idealRayProjection,
    MonoidHom.comp_apply,
    primeToIdealMap_finitePrimeIdele]

/-- The idèle-class/full-idèle ray-class equivalence evaluates on a
double quotient representative by forgetting the intermediate
principal-idèle quotient. -/
@[simp]
theorem rayClassGroupEquivIdeleQuotient_mk_mk
    (m : RayClass.Modulus K)
    (a : IdeleGroup K) :
    RayClass.rayClassGroupEquivIdeleQuotient m
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      QuotientGroup.mk'
        (RayClass.Modulus.ideleCongruenceSubgroup m ⊔
          IdeleGroup.principalSubgroup K) a := by
  exact
    QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk
      (IdeleGroup.principalSubgroup K)
      (RayClass.Modulus.ideleCongruenceSubgroup m ⊔
        IdeleGroup.principalSubgroup K)
      le_sup_right a

/-- The canonical idelic-to-ideal ray-class equivalence sends a
prime-to-modulus idèle class to the ideal ray class of its fractional
ideal. -/
@[simp]
theorem rayClassGroupEquivIdealRayClassGroup_mk_primeTo
    (m : RayClass.Modulus K)
    (a : RayClass.idelePrimeToModulusSubgroup m) :
    RayClass.rayClassGroupEquivIdealRayClassGroup m
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (a : IdeleGroup K))) =
      RayClass.idealRayProjection m a := by
  change
    RayClass.quotientRaySubgroupEquivIdealRayClassGroup m
        ((RayClass.quotientRaySubgroupEquivIdeleRayQuotient m).symm
          (RayClass.rayClassGroupEquivIdeleQuotient m
            (QuotientGroup.mk'
              (RayClass.Modulus.congruenceSubgroup m)
              (QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K)
                (a : IdeleGroup K))))) =
      RayClass.idealRayProjection m a
  rw [rayClassGroupEquivIdeleQuotient_mk_mk]
  change
    RayClass.quotientRaySubgroupEquivIdealRayClassGroup m
        ((RayClass.quotientRaySubgroupEquivIdeleRayQuotient m).symm
          (RayClass.primeToRayClassProjection m a)) =
      RayClass.idealRayProjection m a
  rw [← RayClass.quotientRaySubgroupEquivIdeleRayQuotient_mk m a,
    MulEquiv.symm_apply_apply,
    RayClass.quotientRaySubgroupEquivIdealRayClassGroup_mk]

end GenericPrimeIdele

variable {K : Type} [Field K] [NumberField K]

/-- The ideal Artin map of the fractional ideal attached to a
prime-to-modulus idèle is its direct class in the idèle-class
quotient.  This is the commuting square between the idelic and
ideal-theoretic ray-class constructions. -/
@[simp]
theorem idealArtinMap_primeToIdealMap
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (a : RayClass.idelePrimeToModulusSubgroup m) :
    IdealClassFieldTheory.idealArtinMap m N hm
        (RayClass.primeToIdealMap m a) =
      QuotientGroup.mk' N
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (a : IdeleGroup K)) := by
  let e :=
    RayClass.rayClassGroupEquivIdealRayClassGroup m
  let c : RayClass.RayClassGroup m :=
    QuotientGroup.mk'
      (RayClass.Modulus.congruenceSubgroup m)
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (a : IdeleGroup K))
  have he :
      e c = RayClass.idealRayProjection m a := by
    exact rayClassGroupEquivIdealRayClassGroup_mk_primeTo m a
  have he' :
      e.symm (RayClass.idealRayProjection m a) = c := by
    rw [← he, e.symm_apply_apply]
  change
    IdealClassFieldTheory.rayClassToNormQuotient m N hm
        (e.symm (RayClass.idealRayProjection m a)) =
      QuotientGroup.mk' N
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (a : IdeleGroup K))
  rw [he', IdealClassFieldTheory.rayClassToNormQuotient_mk]

end GlobalClassFields
end GlobalClassFieldTheory

end
