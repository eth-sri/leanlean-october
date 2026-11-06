module

public import ClassFieldTheory.Definitions.GlobalClassFieldTheory.All
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsUnramifiedOutsideModulus
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import ClassFieldTheory.AlgebraicNumberTheory.Ramification.FiniteRamifiedPrimes
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticClassFieldCorrespondence
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.InfiniteAbelianClassFieldCorrespondence
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.ArithmeticIdealArtin
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianKernel
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidueAbelianization
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

















set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

/-!
# Global class field theory implementation

This is the implementation layer for the reader-facing global CFT module.
It collects the existing finite reciprocity, maximal abelian reciprocity,
class-field existence, and infinite correspondence modules without adding
parallel names or existence wrappers.
-/

noncomputable section

namespace ClassFieldTheory.GlobalClassFieldComparison

/-- The idèle class group is commutative.  Keeping this witness public
stabilizes normal-subgroup arguments in exported quotient statements. -/
theorem ideleClassGroupIsMulCommutative
    (K : Type) [Field K] [NumberField K] :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance 2000] ideleClassGroupIsMulCommutative
















































section
variable (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
include K L
/-- The public narrow modulus whose finite part is the actual norm conductor. -/
noncomputable def normConductorRayClassModulus
      : RayClassModulus K := by
  classical
  exact
    { finitePart :=
        GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
          (K := K) (L := L)
      infinitePart := Finset.univ }

/-- The public norm-conductor modulus is the original narrow modulus. -/
theorem normConductorRayClassModulus_original
      :
    rayClassModulusToOriginal K (normConductorRayClassModulus K L) =
      RayClass.Modulus.narrowOfFinite
        (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
          (K := K) (L := L)) := by
  classical
  apply RayClass.Modulus.ext
  · rfl
  · rfl

/-- The actual narrow finite norm conductor, together with every real place,
is a public modulus outside which a finite abelian extension is unramified. -/
theorem normConductorRayClassModulus_unramifiedOutside
      :
    IsUnramifiedOutsideModulus K L (normConductorRayClassModulus K L) := by
  classical
  have hs :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_narrowFiniteConductor_support_eq_ramifiedBaseFinitePlaces
      (K := K) (L := L)
  constructor
  · intro v hv Q hQ hlie
    by_contra hram
    have hQne : Q ≠ ⊥ := by
      intro hbot
      have hunder := hlie.over
      rw [hbot, Ideal.under_bot] at hunder
      exact v.ne_bot hunder
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
      ⟨Q, hQ, hQne⟩
    have hvram : v ∈ _root_.ramifiedBaseFinitePlaces (K := K) (L := L) := by
      rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
      exact ⟨w, hlie, hram⟩
    apply hv
    change v ∈
      (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
        (K := K) (L := L)).support
    rw [hs]
    exact hvram
  · intro v hv hnot
    change (⟨v, hv⟩ : RayClassRealPlace K) ∉ Finset.univ at hnot
    exact (hnot (Finset.mem_univ _)).elim

















/-- The public norm-conductor modulus is a defining modulus for the actual
idèle-class norm subgroup. -/
 theorem normConductorRayClassModulus_isDefining
      :
    RayClass.Modulus.congruenceSubgroup
        (rayClassModulusToOriginal K (normConductorRayClassModulus K L)) ≤
      (_root_.ideleClassNorm K L).range := by
  rw [normConductorRayClassModulus_original K L]
  exact GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_narrowFiniteConductor_isDefiningModulus
    (K := K) (L := L)

/-- Arithmetic global reciprocity, descended to the public ray class group
at the actual narrow norm conductor. -/
noncomputable def normConductorArtin
      :
    RayClassGroup (normConductorRayClassModulus K L) →* (L ≃ₐ[K] L) := by
  let m := normConductorRayClassModulus K L
  let m' := rayClassModulusToOriginal K m
  have hm : RayClass.Modulus.congruenceSubgroup m' ≤
      (_root_.ideleClassNorm K L).range := by
    exact normConductorRayClassModulus_isDefining K L
  exact (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv
      K L).toMulEquiv.toMonoidHom.comp
    ((GlobalClassFieldTheory.IdealClassFieldTheory.idealRayClassArtinMap
      m' ((_root_.ideleClassNorm K L).range) hm).comp
        (rayClassGroupEquivOriginal K m).toMonoidHom)

/-- The conductor ray-class Artin map is onto the finite abelian Galois group. -/
theorem normConductorArtin_surjective
      :
    Function.Surjective (normConductorArtin K L) := by
  unfold normConductorArtin
  exact (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv
    K L).surjective.comp
      ((GlobalClassFieldTheory.IdealClassFieldTheory.idealRayClassArtinMap_surjective
        (rayClassModulusToOriginal K (normConductorRayClassModulus K L))
        ((_root_.ideleClassNorm K L).range)
        (normConductorRayClassModulus_isDefining K L)).comp
        (rayClassGroupEquivOriginal K (normConductorRayClassModulus K L)).surjective)

/-- At a prime away from the norm conductor, the public Artin map agrees
with the arithmetic prime Artin element of the original idèle theory. -/
theorem normConductorArtin_prime
     
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ (normConductorRayClassModulus K L).finitePart.support) :
    normConductorArtin K L
        (rayClassOfFinitePrime (normConductorRayClassModulus K L) v hv) =
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v := by
  let m := normConductorRayClassModulus K L
  let m' := rayClassModulusToOriginal K m
  have hm : RayClass.Modulus.congruenceSubgroup m' ≤
      (_root_.ideleClassNorm K L).range := by
    exact normConductorRayClassModulus_isDefining K L
  have hv' : v ∉ m'.finitePart.support := hv
  change
    (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv K L)
      (GlobalClassFieldTheory.IdealClassFieldTheory.idealRayClassArtinMap
        m' ((_root_.ideleClassNorm K L).range) hm
        (rayClassGroupEquivOriginal K m (rayClassOfFinitePrime m v hv))) = _
  rw [rayClassGroupEquivOriginal_prime K m v hv]
  change GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap
      (K := K) (L := L) m' hm
      (RayClass.primeToModulusIdeal m' v hv') = _
  exact GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_primeIdeal_eq_arithmeticFinitePlacePrimeArtin
    (K := K) (L := L) m' hm v hv'
end



















































end ClassFieldTheory.GlobalClassFieldComparison

end
