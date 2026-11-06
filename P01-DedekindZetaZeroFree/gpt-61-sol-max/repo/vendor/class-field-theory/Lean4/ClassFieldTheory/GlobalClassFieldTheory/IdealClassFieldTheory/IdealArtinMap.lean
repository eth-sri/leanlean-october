module

public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealNorm
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfinitePlaceArtin

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# The ideal-theoretic Artin map

Let `N ≤ C_K` be a class-field norm subgroup and let `m` be a defining
modulus, so `C_K^m ≤ N`.  The idelic quotient map then factors through the
ideal ray class group.  Composing with the projection from ideals prime to
`m` gives the ideal-theoretic Artin map.  This file proves its surjectivity,
identifies its kernel, and records the exact sequence.

The target is kept as the concrete reciprocity quotient `C_K / N`; global
reciprocity identifies this quotient with the corresponding abelian Galois
group.
-/

open scoped NumberField BigOperators NumberField.LiesOver

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField

variable {K : Type} [Field K] [NumberField K]

local instance
    idealArtinMap_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance ideleClassSubgroupNormal
    (N : Subgroup (IdeleClassGroup K)) : N.Normal :=
  N.normal_of_isMulCommutative

section
variable (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
include m N hm
/-- The quotient map from the ray class group modulo a defining modulus
to the class-field reciprocity quotient. -/
def rayClassToNormQuotient
      :
    RayClass.RayClassGroup m →*
      IdeleClassGroup K ⧸ N :=
  QuotientGroup.map
    (RayClass.Modulus.congruenceSubgroup m) N
    (MonoidHom.id (IdeleClassGroup K)) hm

/-- The ray-class quotient map sends the class of an idele class to its
class modulo the norm subgroup. -/
@[simp]
theorem rayClassToNormQuotient_mk
     
    (c : IdeleClassGroup K) :
    rayClassToNormQuotient m N hm
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m) c) =
      QuotientGroup.mk' N c :=
  rfl

/-- The quotient map attached to a defining modulus is surjective. -/
theorem rayClassToNormQuotient_surjective
      :
    Function.Surjective
      (rayClassToNormQuotient m N hm) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro c
  exact
    ⟨QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup m) c, rfl⟩

/-- The Artin map on the ideal ray class group, obtained from the
idele-theoretic reciprocity quotient. -/
def idealRayClassArtinMap
      :
    RayClass.IdealRayClassGroup m →*
      IdeleClassGroup K ⧸ N :=
  (rayClassToNormQuotient m N hm).comp
    (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm.toMonoidHom

/-- The ideal-ray-class Artin map is surjective. -/
theorem idealRayClassArtinMap_surjective
      :
    Function.Surjective
      (idealRayClassArtinMap m N hm) := by
  exact
    (rayClassToNormQuotient_surjective m N hm).comp
      (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm.surjective

/-- The Artin map on fractional ideals prime to `m`. -/
def idealArtinMap
      :
    RayClass.primeToModulusIdeals m →*
      IdeleClassGroup K ⧸ N :=
  (idealRayClassArtinMap m N hm).comp
    (QuotientGroup.mk'
      (RayClass.principalRayIdealSubgroup m))












































































































/-- The ideal group `H_m` attached to `N`: precisely the ideals whose
Artin class is trivial. -/
def idealArtinKernel
      :
    Subgroup (RayClass.primeToModulusIdeals m) :=
  (idealArtinMap m N hm).ker
end




















section NormDefinedFiniteKernel

variable
    {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

























































































































































































































































































































































































































end NormDefinedFiniteKernel

section NormDefinedKernel

variable
    {L : Type} [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]


















end NormDefinedKernel

/-- The Artin map on ideals is surjective. -/
theorem idealArtinMap_surjective
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    Function.Surjective (idealArtinMap m N hm) := by
  exact
    (idealRayClassArtinMap_surjective m N hm).comp
      (QuotientGroup.mk'_surjective
        (RayClass.principalRayIdealSubgroup m))













section ActualGaloisArtin

variable
    {L : Type} [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The ideal-theoretic Artin map with its actual Galois-group target.

For a defining modulus of the genuine norm subgroup
`N_{L/K} C_L`, this is the quotient-valued ideal Artin map followed by
the global norm-residue equivalence
`C_K / N_{L/K} C_L ≃ Gal(L/K)`. -/
noncomputable def idealArtinGaloisMap
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m →*
      (L ≃ₐ[K] L) :=
  (AddEquiv.toMultiplicative
      (Reciprocity.globalNormResidueEquiv K L)).toMonoidHom.comp
    (idealArtinMap m
      ((_root_.ideleClassNorm K L).range) hm)

/-- Evaluation of the actual ideal Artin map is the global
norm-residue equivalence applied to the quotient-valued ideal Artin
class. -/
@[simp]
theorem idealArtinGaloisMap_apply
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    idealArtinGaloisMap (K := K) (L := L) m hm a =
      Additive.toMul
        (Reciprocity.globalNormResidueEquiv K L
          (Additive.ofMul
            (idealArtinMap m
              ((_root_.ideleClassNorm K L).range) hm a))) :=
  rfl

































































end ActualGaloisArtin

end IdealClassFieldTheory
end GlobalClassFieldTheory

end
