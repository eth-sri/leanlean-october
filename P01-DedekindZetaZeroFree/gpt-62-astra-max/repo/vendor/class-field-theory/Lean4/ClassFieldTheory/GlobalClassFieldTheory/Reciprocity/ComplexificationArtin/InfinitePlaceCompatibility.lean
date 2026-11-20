module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.OverextensionArtin
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturality

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Infinite-place local-global Artin compatibility

This module compares the real fixed place and the original ramified place,
then transports the special overextension computation through global
norm-residue naturality.
-/

open scoped Classical IsMulCommutative
open NumberField
open IdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

local instance
    infinitePlaceCompatibilityIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The real infinite place of the conjugation fixed field obtained
by restricting the concrete complex place of the overfield. -/
noncomputable def ramifiedInfinitePlaceRealFixedPlace
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    InfinitePlace
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  (infinitePlaceComplexificationOverfieldComplexPlace
      (K := K) (L := L) v).comap
    (algebraMap
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v))

omit [NumberField K] [FiniteDimensional K L] in
/-- The fixed-field place is genuinely real: every element of the
fixed field is fixed by ambient complex conjugation. -/
theorem ramifiedInfinitePlaceRealFixedPlace_isReal
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    (ramifiedInfinitePlaceRealFixedPlace
      (K := K) (L := L) v hRamified).IsReal := by
  let E :=
    infinitePlaceComplexificationOverfield
      (K := K) (L := L) v
  let K' :=
    ramifiedInfinitePlaceRealFixedField
        v hRamified
  refine ⟨(E.val.toRingHom.comp (algebraMap K' E)), ?_, ?_⟩
  · rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx := (IntermediateField.mem_fixedField_iff _ _).1
          x.property
    have hxc :=
      hx
        (ramifiedInfinitePlaceOverfieldConjugation
            v hRamified)
        (Subgroup.mem_zpowers
          (ramifiedInfinitePlaceOverfieldConjugation
              v hRamified))
    have hconj := ramifiedInfinitePlaceOverfieldConjugation_apply
            v hRamified (x : E)
    rw [ComplexEmbedding.conjugate_coe_eq]
    change
      star (E.val.toRingHom (algebraMap K' E x)) =
        E.val.toRingHom (algebraMap K' E x)
    rw [IntermediateField.algebraMap_apply]
    exact hconj.symm.trans (congrArg
      (fun z : E => E.val.toRingHom z)
      hxc)
  · rfl

omit [FiniteDimensional K L] in
/-- Restricting the concrete real fixed-field place to the original
base recovers the prescribed ramified place `v`. -/
theorem infinitePlaceBelow_ramifiedInfinitePlaceRealFixedPlace
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    infinitePlaceBelow (K := K)
        (ramifiedInfinitePlaceRealFixedPlace
          (K := K) (L := L) v hRamified) =
      v := by
  apply InfinitePlace.ext
  intro x
  change
    ‖((algebraMap
          (ramifiedInfinitePlaceRealFixedField
              v hRamified)
          (infinitePlaceComplexificationOverfield
              v)
          (algebraMap K
            (ramifiedInfinitePlaceRealFixedField
                v hRamified) x) :
        infinitePlaceComplexificationOverfield
            v) : ℂ)‖ =
      v x
  rw [← IsScalarTower.algebraMap_apply K
    (ramifiedInfinitePlaceRealFixedField
        v hRamified)
    (infinitePlaceComplexificationOverfield
        v)]
  change
    ‖InfinitePlace.embedding
        (chosenInfinitePlaceAbove v)
        (algebraMap K L x)‖ =
      v x
  rw [InfinitePlace.norm_embedding_eq]
  exact
    congrArg
      (fun q : InfinitePlace K => q x)
      (chosenInfinitePlaceAbove_comap v)

omit [NumberField K] [FiniteDimensional K L] in
/-- The chosen place of the special overextension above its concrete
fixed-field place is ramified. -/
theorem
    ramifiedInfinitePlaceOverextension_chosenPlace_isRamified
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    (chosenInfinitePlaceAbove
      (L :=
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
      (ramifiedInfinitePlaceRealFixedPlace
        (K := K) (L := L) v hRamified)).IsRamified
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) := by
  rw [InfinitePlace.isRamified_iff,
    chosenInfinitePlaceAbove_comap

      (ramifiedInfinitePlaceRealFixedPlace
          v hRamified)]
  exact
    ⟨IsTotallyComplex.isComplex _,
      ramifiedInfinitePlaceRealFixedPlace_isReal
          v hRamified⟩

omit [NumberField K] [FiniteDimensional K L] in
/-- At the concrete real fixed-field place, the local Artin symbol of
negative one is the distinguished ambient complex conjugation. -/
theorem
    ramifiedInfinitePlaceOverextension_localArtin_neg_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    chosenInfinitePlaceArtinMonoidHom
        (K :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        (ramifiedInfinitePlaceRealFixedPlace
          (K := K) (L := L) v hRamified)
        (-1 :
          (ramifiedInfinitePlaceRealFixedPlace
            (K := K) (L := L) v hRamified).Completionˣ) =
      ramifiedInfinitePlaceOverextensionConjugation
        (K := K) (L := L) v hRamified := by
  apply
    ramifiedInfinitePlaceOverextension_galois_eq_of_ne_one
        v hRamified
  · have hConj :=
      chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified

        (ramifiedInfinitePlaceRealFixedPlace
            v hRamified)
        (ramifiedInfinitePlaceOverextension_chosenPlace_isRamified
            v hRamified)
    exact
      (ComplexEmbedding.isConj_ne_one_iff hConj).2
        (InfinitePlace.isComplex_iff.mp
          (IsTotallyComplex.isComplex
            (chosenInfinitePlaceAbove

              (ramifiedInfinitePlaceRealFixedPlace
                  v hRamified))))
  · intro hc
    apply
      ramifiedInfinitePlaceOverextensionCyclotomicRestriction_conjugation_ne_one
          v hRamified
    rw [hc, map_one]

omit [NumberField K] [FiniteDimensional K L] in
/-- The canonical global norm-residue value of the concrete
fixed-field one-place negative-one class is ambient complex
conjugation. -/
theorem
    ramifiedInfinitePlaceOverextension_globalNormResidue_neg_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    globalNormResidueMonoidHom
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        (IdeleGroup.infinitePlaceIdeleClass
          (ramifiedInfinitePlaceRealFixedPlace
            (K := K) (L := L) v hRamified)
          (-1 :
            (ramifiedInfinitePlaceRealFixedPlace
              (K := K) (L := L) v hRamified).Completionˣ)) =
      ramifiedInfinitePlaceOverextensionConjugation
        (K := K) (L := L) v hRamified := by
  rw [
    globalNormResidueMonoidHom_ramifiedInfinitePlaceOverextension_infinitePlaceIdeleClass,
    ramifiedInfinitePlaceOverextension_localArtin_neg_one]

/-- Restriction from the complex-conjugation overextension back to
the original finite abelian extension. -/
noncomputable def ramifiedInfinitePlaceOverextensionRestriction
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal(
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) /
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)) →*
      Gal(L / K) :=
  (AlgEquiv.restrictNormalHom L).comp
    (AlgEquiv.restrictScalarsHom K)

omit [FiniteDimensional K L] in
/-- Restricting ambient complex conjugation from `L(i)` to `L`
recovers the actual chosen local Artin symbol of negative one at the
original ramified place. -/
theorem ramifiedInfinitePlaceOverextensionRestriction_conjugation
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceOverextensionRestriction
        (K := K) (L := L) v hRamified
        (ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (-1 : v.Completionˣ) := by
  apply AlgEquiv.ext
  intro x
  apply
    (algebraMap L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)).injective
  change
    algebraMap L
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        ((AlgEquiv.restrictNormalHom L
          ((ramifiedInfinitePlaceOverextensionConjugation
            (K := K) (L := L) v hRamified).restrictScalars K)) x) =
      algebraMap L
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        (chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (-1 : v.Completionˣ) x)
  have hrestrict :
      algebraMap L
          (infinitePlaceComplexificationOverfield
              v)
          ((AlgEquiv.restrictNormalHom L
            ((ramifiedInfinitePlaceOverextensionConjugation
                v hRamified).restrictScalars K)) x) =
        (ramifiedInfinitePlaceOverextensionConjugation
            v hRamified).restrictScalars K
          (algebraMap L
            (infinitePlaceComplexificationOverfield
                v) x) := by
    exact
      AlgEquiv.restrictNormal_commutes
        ((ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified).restrictScalars K)
        L x
  rw [hrestrict]
  apply Subtype.ext
  change
    star
        (InfinitePlace.embedding
          (chosenInfinitePlaceAbove v) x) =
      InfinitePlace.embedding
        (chosenInfinitePlaceAbove v)
        (chosenInfinitePlaceArtinMonoidHom
            v
          (-1 : v.Completionˣ) x)
  exact
    (chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
        v hRamified).eq x |>.symm

/-- A rational-separable-closure embedding of the complexification
overfield extending the standard embedding of its original top field. -/
noncomputable def
    infinitePlaceComplexificationOverfieldSeparableClosureEmbedding
    (v : InfinitePlace K) :
    infinitePlaceComplexificationOverfield
        (K := K) (L := L) v →ₐ[ℚ]
      SeparableClosure ℚ :=
  Classical.choose
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ)
      (L := L)
      (E :=
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
      (M := SeparableClosure ℚ)
      (AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L))

omit [NumberField K] [FiniteDimensional K L] in
/-- The separable-closure embedding of the complexification overfield
restricts to the standard embedding of its original top field. -/
theorem
    infinitePlaceComplexificationOverfieldSeparableClosureEmbedding_restrictDomain
    (v : InfinitePlace K) :
    (infinitePlaceComplexificationOverfieldSeparableClosureEmbedding
      (K := K) (L := L) v).domRestrict L =
        AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L :=
  Classical.choose_spec
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ)
      (L := L)
      (E :=
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
      (M := SeparableClosure ℚ)
      (AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L))

omit [NumberField K] [FiniteDimensional K L] in
/-- The explicitly embedded norm-residue map for the quadratic
overextension has the genuine idele-class norm range as its kernel. -/
theorem
    ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_eq_one_iff
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (j :
      infinitePlaceComplexificationOverfield
          (K := K) (L := L) v →ₐ[ℚ]
        SeparableClosure ℚ)
    (c :
      IdeleClassGroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)) :
    globalNormResidueMonoidHomOfEmbedding
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        j c =
      1 ↔
    c ∈
      (_root_.ideleClassNorm
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)).range := by
  let e :=
    AddEquiv.toMultiplicative
      (globalNormResidueEquivOfEmbedding
        (ramifiedInfinitePlaceRealFixedField
            v hRamified)
        (infinitePlaceComplexificationOverfield
            v)
        j)
  change
    e (QuotientGroup.mk'
          (_root_.ideleClassNorm
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified)
            (infinitePlaceComplexificationOverfield
              (K := K) (L := L) v)).range c) =
        1 ↔
      c ∈
        (_root_.ideleClassNorm
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)).range
  constructor
  · intro h
    refine (QuotientGroup.eq_one_iff c).1 ?_
    apply e.injective
    exact h.trans (map_one e).symm
  · intro hc
    calc
      e (QuotientGroup.mk'
          (_root_.ideleClassNorm
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified)
            (infinitePlaceComplexificationOverfield
              (K := K) (L := L) v)).range c) = e 1 :=
        congrArg e ((QuotientGroup.eq_one_iff c).2 hc)
      _ = 1 := map_one e

omit [NumberField K] [FiniteDimensional K L] in
/-- For every rational-separable-closure embedding, the norm-residue
value of the concrete upper negative-one one-place class is ambient
complex conjugation.  The point is independent of the embedding
because the upper Galois group is the actual two-element group and all
these maps have the same genuine norm kernel. -/
theorem
    ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_neg_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (j :
      infinitePlaceComplexificationOverfield
          (K := K) (L := L) v →ₐ[ℚ]
        SeparableClosure ℚ) :
    globalNormResidueMonoidHomOfEmbedding
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        j
        (IdeleGroup.infinitePlaceIdeleClass
          (ramifiedInfinitePlaceRealFixedPlace
            (K := K) (L := L) v hRamified)
          (-1 :
            (ramifiedInfinitePlaceRealFixedPlace
              (K := K) (L := L) v hRamified).Completionˣ)) =
      ramifiedInfinitePlaceOverextensionConjugation
        (K := K) (L := L) v hRamified := by
  rcases
      ramifiedInfinitePlaceOverextension_eq_one_or_conjugation
          v hRamified
        (globalNormResidueMonoidHomOfEmbedding
          (ramifiedInfinitePlaceRealFixedField
              v hRamified)
          (infinitePlaceComplexificationOverfield
              v)
          j
          (IdeleGroup.infinitePlaceIdeleClass
            (ramifiedInfinitePlaceRealFixedPlace
                v hRamified)
            (-1 :
              (ramifiedInfinitePlaceRealFixedPlace
                  v hRamified).Completionˣ))) with
    htrivial | hconjugation
  · exfalso
    have hstandard :
        globalNormResidueMonoidHom
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified)
            (infinitePlaceComplexificationOverfield
              (K := K) (L := L) v)
            (IdeleGroup.infinitePlaceIdeleClass
              (ramifiedInfinitePlaceRealFixedPlace
                (K := K) (L := L) v hRamified)
              (-1 :
                (ramifiedInfinitePlaceRealFixedPlace
                  (K := K) (L := L) v hRamified).Completionˣ)) =
          1 :=
      (globalNormResidueMonoidHom_eq_one_iff
        (K :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        _).2 ((ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_eq_one_iff
          v hRamified j _).mp htrivial)
    rw [
      ramifiedInfinitePlaceOverextension_globalNormResidue_neg_one]
      at hstandard
    apply
      ramifiedInfinitePlaceOverextensionCyclotomicRestriction_conjugation_ne_one
          v hRamified
    rw [hstandard, map_one]
  · exact hconjugation

section

variable (v : InfinitePlace K)

/-- The base global norm-residue value at the negative-one class of `v`. -/
noncomputable def ramifiedInfinitePlaceGlobalNormResidueNegOneValue :
    Gal(L / K) :=
  globalNormResidueMonoidHom K L
    (IdeleGroup.infinitePlaceIdeleClass v (-1 : v.Completionˣ))

/-- The chosen local Artin value at negative one at `v`. -/
noncomputable def ramifiedInfinitePlaceLocalArtinNegOneValue :
    Gal(L / K) :=
  chosenInfinitePlaceArtinMonoidHom
    (K := K) (L := L) v (-1 : v.Completionˣ)

/-- The embedding of `L` induced by the chosen embedding of its
complexification overfield. -/
noncomputable def
    infinitePlaceComplexificationLowerSeparableClosureEmbedding :
    L →ₐ[ℚ] SeparableClosure ℚ :=
  (infinitePlaceComplexificationOverfieldSeparableClosureEmbedding
      (K := K) (L := L) v).comp
    (IsScalarTower.toAlgHom ℚ L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v))

end

omit [NumberField K] [FiniteDimensional K L] in
/-- The induced lower embedding is the standard number-field embedding. -/
theorem
    infinitePlaceComplexificationLowerSeparableClosureEmbedding_eq_standard
    (v : InfinitePlace K) :
    infinitePlaceComplexificationLowerSeparableClosureEmbedding
        (K := K) (L := L) v =
      AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L := by
  simpa only [
    infinitePlaceComplexificationLowerSeparableClosureEmbedding,
    AlgHom.domRestrict] using
    infinitePlaceComplexificationOverfieldSeparableClosureEmbedding_restrictDomain
      (K := K) (L := L) v

/-- The upper negative-one idele class used in the overextension diamond. -/
noncomputable def ramifiedInfinitePlaceOverextensionNegOneIdeleClass
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IdeleClassGroup
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  IdeleGroup.infinitePlaceIdeleClass
    (ramifiedInfinitePlaceRealFixedPlace
      (K := K) (L := L) v hRamified)
    (-1 :
      (ramifiedInfinitePlaceRealFixedPlace
        (K := K) (L := L) v hRamified).Completionˣ)

/-- The upper global norm-residue value in the overextension diamond. -/
noncomputable def
    ramifiedInfinitePlaceOverextensionGlobalNormResidueNegOneValue
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal(
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) /
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)) :=
  globalNormResidueMonoidHomOfEmbedding
    (ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified)
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)
    (infinitePlaceComplexificationOverfieldSeparableClosureEmbedding
      (K := K) (L := L) v)
    (ramifiedInfinitePlaceOverextensionNegOneIdeleClass
      (K := K) (L := L) v hRamified)

section

variable (v : InfinitePlace K)

/-- The upper norm-residue value after actual Galois restriction. -/
noncomputable def
    ramifiedInfinitePlaceRestrictedOverextensionNormResidueNegOneValue
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal(L / K) :=
  ramifiedInfinitePlaceOverextensionRestriction
    (K := K) (L := L) v hRamified
    (ramifiedInfinitePlaceOverextensionGlobalNormResidueNegOneValue
      (K := K) (L := L) v hRamified)

/-- The lower norm-residue value of the normed upper negative-one class. -/
noncomputable def
    ramifiedInfinitePlaceNormedOverextensionNormResidueNegOneValue
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal(L / K) :=
  globalNormResidueMonoidHomOfEmbedding K L
    (infinitePlaceComplexificationLowerSeparableClosureEmbedding
      (K := K) (L := L) v)
    (_root_.ideleClassNorm K
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (ramifiedInfinitePlaceOverextensionNegOneIdeleClass
        (K := K) (L := L) v hRamified))

private theorem ramifiedInfinitePlace_normResidueDiamond_neg_one
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceRestrictedOverextensionNormResidueNegOneValue
        (K := K) (L := L) v hRamified =
      ramifiedInfinitePlaceNormedOverextensionNormResidueNegOneValue
        (K := K) (L := L) v hRamified := DFunLike.congr_fun
      (globalNormResidueMonoidHomOfEmbedding_norm_restriction
        (K := K) (L := L)
        (K' :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L' :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        (infinitePlaceComplexificationOverfieldSeparableClosureEmbedding
          (K := K) (L := L) v))
      (ramifiedInfinitePlaceOverextensionNegOneIdeleClass
        (K := K) (L := L) v hRamified)

end

omit [FiniteDimensional K L] in
private theorem
    ramifiedInfinitePlace_restrictedOverextensionNormResidue_neg_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceRestrictedOverextensionNormResidueNegOneValue
        (K := K) (L := L) v hRamified =
      ramifiedInfinitePlaceLocalArtinNegOneValue
        (K := K) (L := L) v := by
  rw [
    ramifiedInfinitePlaceRestrictedOverextensionNormResidueNegOneValue,
    ramifiedInfinitePlaceOverextensionGlobalNormResidueNegOneValue,
    ramifiedInfinitePlaceOverextensionNegOneIdeleClass,
    ramifiedInfinitePlaceLocalArtinNegOneValue,
    ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_neg_one,
    ramifiedInfinitePlaceOverextensionRestriction_conjugation]

private theorem ramifiedInfinitePlace_normedNormResidue_neg_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceNormedOverextensionNormResidueNegOneValue
        (K := K) (L := L) v hRamified =
      ramifiedInfinitePlaceGlobalNormResidueNegOneValue
        (K := K) (L := L) v := by
  rw [
    ramifiedInfinitePlaceNormedOverextensionNormResidueNegOneValue,
    infinitePlaceComplexificationLowerSeparableClosureEmbedding_eq_standard,
    ← globalNormResidueMonoidHom_eq_ofEmbedding_standard,
    ramifiedInfinitePlaceOverextensionNegOneIdeleClass,
    IdeleGroup.ideleClassNorm_infinitePlaceIdeleClass_neg_one_of_isReal

      (ramifiedInfinitePlaceRealFixedPlace
          v hRamified)
      (ramifiedInfinitePlaceRealFixedPlace_isReal
          v hRamified),
    infinitePlaceBelow_ramifiedInfinitePlaceRealFixedPlace,
    ramifiedInfinitePlaceGlobalNormResidueNegOneValue]

/-- At every ramified real place of a finite abelian extension, the
canonical global norm-residue symbol of the one-place negative-one
idele class is the actual chosen local Artin symbol.

The proof is the concrete complex-conjugation overextension diamond:
the upper equality is the rational fourth-root product formula, the
vertical map on idele classes is the genuine one-place norm, and the
vertical map on Galois groups is actual restriction. -/
@[simp]
theorem
    globalNormResidueMonoidHom_infinitePlaceIdeleClass_neg_one_of_ramified
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceGlobalNormResidueNegOneValue
        (K := K) (L := L) v =
      ramifiedInfinitePlaceLocalArtinNegOneValue
        (K := K) (L := L) v := (ramifiedInfinitePlace_normedNormResidue_neg_one
        v hRamified).symm |>.trans
      ((ramifiedInfinitePlace_normResidueDiamond_neg_one
          v hRamified).symm.trans
        (ramifiedInfinitePlace_restrictedOverextensionNormResidue_neg_one
            v hRamified))

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory

end
