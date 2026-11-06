module

public import ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealFactorization
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormLocalOrder
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfinitePlaceArtin

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


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

/-- The quotient map from the ray class group modulo a defining modulus
to the class-field reciprocity quotient. -/
def rayClassToNormQuotient
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    RayClass.RayClassGroup m →*
      IdeleClassGroup K ⧸ N :=
  QuotientGroup.map
    (RayClass.Modulus.congruenceSubgroup m) N
    (MonoidHom.id (IdeleClassGroup K)) hm

/-- The ray-class quotient map sends the class of an idele class to its
class modulo the norm subgroup. -/
@[simp]
theorem rayClassToNormQuotient_mk
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (c : IdeleClassGroup K) :
    rayClassToNormQuotient m N hm
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m) c) =
      QuotientGroup.mk' N c :=
  rfl

/-- The quotient map attached to a defining modulus is surjective. -/
theorem rayClassToNormQuotient_surjective
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
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
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    RayClass.IdealRayClassGroup m →*
      IdeleClassGroup K ⧸ N :=
  (rayClassToNormQuotient m N hm).comp
    (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm.toMonoidHom

/-- The ideal-ray-class Artin map is surjective. -/
theorem idealRayClassArtinMap_surjective
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    Function.Surjective
      (idealRayClassArtinMap m N hm) := by
  exact
    (rayClassToNormQuotient_surjective m N hm).comp
      (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm.surjective

/-- The Artin map on fractional ideals prime to `m`. -/
def idealArtinMap
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    RayClass.primeToModulusIdeals m →*
      IdeleClassGroup K ⧸ N :=
  (idealRayClassArtinMap m N hm).comp
    (QuotientGroup.mk'
      (RayClass.principalRayIdealSubgroup m))

/-- The ideal group `H_m` attached to `N`: precisely the ideals whose
Artin class is trivial. -/
def idealArtinKernel
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    Subgroup (RayClass.primeToModulusIdeals m) :=
  (idealArtinMap m N hm).ker
