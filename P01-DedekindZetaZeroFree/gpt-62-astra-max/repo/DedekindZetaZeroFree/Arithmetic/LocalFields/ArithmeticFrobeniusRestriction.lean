module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.UnramifiedInertiaCriterion

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField
open IsDedekindDomain

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (E : IntermediateField K L) (p : HeightOneSpectrum (𝓞 K))
    (wE : HeightOneSpectrum (𝓞 ↥E)) (wL : HeightOneSpectrum (𝓞 L)) (hwE : wE.asIdeal.LiesOver p.asIdeal)
    (hwL : wL.asIdeal.LiesOver wE.asIdeal)

include hwE hwL in
theorem isArithFrobAt_arithmeticFrobeniusRestrictIntermediate :
    IsArithFrobAt (𝓞 K)
      (AlgEquiv.restrictNormalHom ↥E (ClassFieldTheory.arithmeticFrobeniusAt (K := K) wL))
      wE.asIdeal := by
  letI := hwE
  letI := hwL
  haveI : wL.asIdeal.LiesOver p.asIdeal := Ideal.LiesOver.trans wL.asIdeal wE.asIdeal p.asIdeal
  have hL := IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) wL.asIdeal
  intro x
  apply (Ideal.mem_of_liesOver wL.asIdeal wE.asIdeal _).mpr
  rw [map_sub, map_pow]
  let algebraMap₀ := algebraMap (𝓞 ↥E) (𝓞 L)
  have hcomm : algebraMap₀
      ((AlgEquiv.restrictNormalHom ↥E (ClassFieldTheory.arithmeticFrobeniusAt (K := K) wL)) • x) =
      ClassFieldTheory.arithmeticFrobeniusAt (K := K) wL • (algebraMap₀ x) := by
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes (ClassFieldTheory.arithmeticFrobeniusAt (K := K) wL) ↥E (x : ↥E)
  change algebraMap₀
      ((AlgEquiv.restrictNormalHom ↥E (ClassFieldTheory.arithmeticFrobeniusAt (K := K) wL)) • x) -
      algebraMap₀ x ^ Nat.card ((𝓞 K) ⧸ wE.asIdeal.under (𝓞 K)) ∈ wL.asIdeal
  rw [hcomm, ← Ideal.over_def wE.asIdeal p.asIdeal, Ideal.over_def wL.asIdeal p.asIdeal]
  exact hL _

include hwE hwL in
theorem arithmeticFrobeniusRestrictUnramifiedBottom
    (hE : Algebra.IsUnramifiedAt (𝓞 K) wE.asIdeal) :
    AlgEquiv.restrictNormalHom ↥E (ClassFieldTheory.arithmeticFrobeniusAt (K := K) wL) =
      ClassFieldTheory.arithmeticFrobeniusAt (K := K) wE := by
  have hratio := (isArithFrobAt_arithmeticFrobeniusRestrictIntermediate E p wE wL hwE hwL).mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 K) (↥E ≃ₐ[K] ↥E) wE.asIdeal)
  rw [(unramifiedIffInertiaBot p wE hwE).mp hE, Subgroup.mem_bot] at hratio
  exact mul_inv_eq_one.mp hratio

end DedekindZetaZeroFree.AbelianQuotient
