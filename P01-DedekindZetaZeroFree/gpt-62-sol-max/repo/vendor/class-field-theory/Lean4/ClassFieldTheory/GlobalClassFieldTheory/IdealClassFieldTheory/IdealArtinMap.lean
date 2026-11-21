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

variable (m : RayClass.Modulus K) (N : Subgroup (IdeleClassGroup K))
  (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
include hm

/-- The quotient map from the ray class group modulo a defining modulus
to the class-field reciprocity quotient. -/
def rayClassToNormQuotient :
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
theorem rayClassToNormQuotient_surjective :
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
def idealRayClassArtinMap :
    RayClass.IdealRayClassGroup m →*
      IdeleClassGroup K ⧸ N :=
  (rayClassToNormQuotient m N hm).comp
    (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm.toMonoidHom

/-- The ideal-ray-class Artin map is surjective. -/
theorem idealRayClassArtinMap_surjective :
    Function.Surjective
      (idealRayClassArtinMap m N hm) := by
  exact
    (rayClassToNormQuotient_surjective m N hm).comp
      (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm.surjective

/-- The Artin map on fractional ideals prime to `m`. -/
def idealArtinMap :
    RayClass.primeToModulusIdeals m →*
      IdeleClassGroup K ⧸ N :=
  (idealRayClassArtinMap m N hm).comp
    (QuotientGroup.mk'
      (RayClass.principalRayIdealSubgroup m))

end

private theorem
    quotientRaySubgroupEquivIdealRayClassGroup_mk
    (m : RayClass.Modulus K)
    (a : RayClass.idelePrimeToModulusSubgroup m) :
    RayClass.quotientRaySubgroupEquivIdealRayClassGroup m
        (QuotientGroup.mk'
          (RayClass.raySubgroupInPrimeTo m) a) =
      RayClass.idealRayProjection m a := by
  exact RayClass.quotientRaySubgroupEquivIdealRayClassGroup_mk m a

private theorem
    quotientRaySubgroupEquivIdeleRayQuotient_mk
    (m : RayClass.Modulus K)
    (a : RayClass.idelePrimeToModulusSubgroup m) :
    RayClass.quotientRaySubgroupEquivIdeleRayQuotient m
        (QuotientGroup.mk'
          (RayClass.raySubgroupInPrimeTo m) a) =
      RayClass.primeToRayClassProjection m a := by
  exact RayClass.quotientRaySubgroupEquivIdeleRayQuotient_mk m a

private theorem rayClassGroupEquivIdeleQuotient_mk_mk
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

private theorem
    rayClassGroupEquivIdealRayClassGroup_mk_primeTo
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
  rw [← quotientRaySubgroupEquivIdeleRayQuotient_mk m a,
    MulEquiv.symm_apply_apply,
    quotientRaySubgroupEquivIdealRayClassGroup_mk]

/-- The ideal Artin map of the fractional ideal attached to a
prime-to-modulus idèle is its class in the idèle-class quotient. -/
@[simp]
theorem idealArtinMap_primeToIdealMap
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (a : RayClass.idelePrimeToModulusSubgroup m) :
    idealArtinMap m N hm
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
    exact
      rayClassGroupEquivIdealRayClassGroup_mk_primeTo m a
  have he' :
      e.symm (RayClass.idealRayProjection m a) = c := by
    rw [← he, e.symm_apply_apply]
  change
    rayClassToNormQuotient m N hm
        (e.symm (RayClass.idealRayProjection m a)) =
      QuotientGroup.mk' N
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (a : IdeleGroup K))
  rw [he', rayClassToNormQuotient_mk]

/-- The ideal group `H_m` attached to `N`: precisely the ideals whose
Artin class is trivial. -/
def idealArtinKernel
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    Subgroup (RayClass.primeToModulusIdeals m) :=
  (idealArtinMap m N hm).ker


section NormDefinedFiniteKernel

variable
    {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- For choosing idèle representatives of ideal norms, retain the finite
part of the ideal-norm lifted modulus and impose positivity at every real
place upstairs.  Its prime-to ideal group is definitionally the same as the
one for `idealNormLiftedModulus`, while positivity makes its idèle norm
prime to the selected infinite part downstairs. -/
noncomputable def normIdeleLiftedModulus
    (m : RayClass.Modulus K) : RayClass.Modulus L :=
  RayClass.Modulus.narrowOfFinite
    (RayClass.idealNormLiftedModulus
      (K := K) (L := L) m).finitePart

private theorem ideleNorm_mem_finitePrimeToModulusSubgroup_aux
    (m : RayClass.Modulus K)
    (a : RayClass.idelePrimeToModulusSubgroup
      (normIdeleLiftedModulus (K := K) (L := L) m)) :
    (IdeleGroup.norm K L (a : IdeleGroup L)).2 ∈
      RayClass.finitePrimeToModulusSubgroup m := by
  let aFinite :
      RayClass.idelePrimeToModulusSubgroup
        (RayClass.idealNormLiftedModulus (K := K) (L := L) m) :=
    ⟨(a : IdeleGroup L), by
      constructor
      · apply
          (RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff
            (RayClass.idealNormLiftedModulus
              (K := K) (L := L) m) _).2
        intro v hv
        have hNoInfinite :
            (RayClass.idealNormLiftedModulus
              (K := K) (L := L) m).infinitePart = ∅ :=
          rfl
        rw [hNoInfinite] at hv
        exact (Finset.notMem_empty _ hv).elim
      · exact a.property.2⟩
  exact
    RayClass.finite_norm_mem_finitePrimeToModulusSubgroup
      (K := K) (L := L) m aFinite

/-- The idèle norm carries idèles prime to the lifted modulus to
idèles prime to the base modulus.  At real places this uses positivity
of both real-real and complex-real local norms. -/
theorem ideleNorm_mem_idelePrimeToModulusSubgroup
    (m : RayClass.Modulus K)
    (a : RayClass.idelePrimeToModulusSubgroup
      (normIdeleLiftedModulus
        (K := K) (L := L) m)) :
    IdeleGroup.norm K L (a : IdeleGroup L) ∈
      RayClass.idelePrimeToModulusSubgroup m := by
  classical
  constructor
  · apply
      (RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff m
        (IdeleGroup.norm K L (a : IdeleGroup L)).1).2
    intro v _hv
    let : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v.1},
        W.1.1.LiesOver v.1.1 :=
      fun W =>
        ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    have hNormComponent :
        IdeleGroup.infiniteComponent v.1
            (IdeleGroup.norm K L (a : IdeleGroup L)) ∈
          RayClass.infinitePositiveSubgroup v.1 := by
      rw [IdeleGroup.infiniteComponent_norm_eq_prod]
      apply Subgroup.prod_mem
      intro W _hW
      apply
        (RayClass.mem_infinitePositiveSubgroup_iff v.1
          (LocalFieldTheory.normUnits
            v.1.Completion W.1.Completion
            (IdeleGroup.infiniteComponent W.1
              (a : IdeleGroup L)))).2
      intro hvReal
      have hbelow :
          W.1.comap (algebraMap K L) = v.1 := by
        simpa only [_root_.infinitePlaceBelow] using W.2
      rcases W.1.isReal_or_isComplex with hWReal | hWComplex
      · have hUpstairs :
            0 <
              InfinitePlace.Completion.ringEquivRealOfIsReal
                hWReal
              (IdeleGroup.infiniteComponent W.1
                  (a : IdeleGroup L) :
                  W.1.Completion) := by
          have hPositive :=
            (RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff
              (normIdeleLiftedModulus
                (K := K) (L := L) m)
              (a : IdeleGroup L).1).1 a.property.1
                ⟨W.1, hWReal⟩ (by exact Finset.mem_univ _)
          exact
            (RayClass.mem_infinitePositiveSubgroup_iff W.1
              (IdeleGroup.infiniteComponent W.1
                (a : IdeleGroup L))).1 hPositive hWReal
        have hNorm :=
          Reciprocity.infinitePlace_normUnits_real_real
            (K := K) (K' := L) v.1 W.1 hbelow
              hvReal hWReal
              (IdeleGroup.infiniteComponent W.1
                (a : IdeleGroup L))
        have hNormVal := congrArg Units.val hNorm
        change
          0 <
            ((Units.mapEquiv
              (InfinitePlace.Completion.ringEquivRealOfIsReal
                hvReal).toMulEquiv)
              (LocalFieldTheory.normUnits
                v.1.Completion W.1.Completion
                (IdeleGroup.infiniteComponent W.1
                  (a : IdeleGroup L))) : ℝ)
        rw [hNormVal]
        change
          0 <
            InfinitePlace.Completion.ringEquivRealOfIsReal
              hWReal
              (IdeleGroup.infiniteComponent W.1
                (a : IdeleGroup L) : W.1.Completion)
        exact hUpstairs
      · simpa only [
            InfinitePlace.Completion.ringEquivRealOfIsReal_apply] using
          Reciprocity.infinitePlace_normUnits_real_complex_pos
            (K := K) (K' := L) v.1 W.1 hbelow
              hvReal hWComplex
              (IdeleGroup.infiniteComponent W.1
                (a : IdeleGroup L))
    simpa only [IdeleGroup.infiniteComponent_apply] using hNormComponent
  · exact ideleNorm_mem_finitePrimeToModulusSubgroup_aux m a

/-- The ordinary idèle norm restricted to the prime-to-modulus
subgroups selected by the lifted modulus. -/
noncomputable def primeToModulusIdeleNorm
    (m : RayClass.Modulus K) :
    RayClass.idelePrimeToModulusSubgroup
        (normIdeleLiftedModulus
          (K := K) (L := L) m) →*
      RayClass.idelePrimeToModulusSubgroup m where
  toFun a :=
    ⟨IdeleGroup.norm K L (a : IdeleGroup L),
      ideleNorm_mem_idelePrimeToModulusSubgroup
        (K := K) (L := L) m a⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (IdeleGroup.norm K L)
  map_mul' a b := by
    apply Subtype.ext
    exact
      (IdeleGroup.norm K L).map_mul
        (a : IdeleGroup L) (b : IdeleGroup L)

/-- The restricted idèle norm and the genuine ideal norm commute with
the prime-to-modulus fractional-ideal maps. -/
@[simp]
theorem primeToIdealMap_primeToModulusIdeleNorm
    (m : RayClass.Modulus K)
    (a : RayClass.idelePrimeToModulusSubgroup
      (normIdeleLiftedModulus
        (K := K) (L := L) m)) :
    RayClass.primeToIdealMap m
        (primeToModulusIdeleNorm
          (K := K) (L := L) m a) =
      RayClass.primeToModulusIdealNorm
        (K := K) (L := L) m
        (RayClass.primeToIdealMap
          (normIdeleLiftedModulus
            (K := K) (L := L) m) a) := by
  apply Subtype.ext
  exact
    IdeleGroup.fractionalIdeal_ideleNorm
      (K := K) (L := L) (a : IdeleGroup L)






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


/-- Passing from the genuine norm quotient to the actual Galois group
does not change the ideal Artin kernel. -/
@[simp]
theorem idealArtinGaloisMap_ker
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    (idealArtinGaloisMap
        (K := K) (L := L) m hm).ker =
      idealArtinKernel m
        ((_root_.ideleClassNorm K L).range) hm := by
  ext a
  let e :=
    AddEquiv.toMultiplicative
      (Reciprocity.globalNormResidueEquiv K L)
  change
    e
          (idealArtinMap m
            ((_root_.ideleClassNorm K L).range) hm a) =
        1 ↔
      idealArtinMap m
          ((_root_.ideleClassNorm K L).range) hm a =
        1
  exact e.map_eq_one_iff


end ActualGaloisArtin

end IdealClassFieldTheory
end GlobalClassFieldTheory

end
