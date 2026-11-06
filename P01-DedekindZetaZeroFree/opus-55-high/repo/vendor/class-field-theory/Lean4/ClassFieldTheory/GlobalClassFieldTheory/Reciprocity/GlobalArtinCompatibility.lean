module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinFiniteSupportApproximation
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.SeparableClosurePadicLift
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicCyclicData
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicAuxiliaryField
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteLocalGlobalArtinCompatibility
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidue

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Compatibility of the global Artin map with global reciprocity

For a finite abelian extension of number fields, the preliminary global
Artin map is the product of the chosen local Artin maps.  The finite-place
and infinite-place compatibility theorems identify every one-place factor
with the canonical global norm-residue map.

Only finitely many finite local Artin factors of an idele are nontrivial.
The finite-support approximation theorem replaces an arbitrary idele by
the product of those one-place ideles modulo an actual relative-idele norm.
It follows that the preliminary global Artin map is exactly the pullback
of the canonical norm-residue map along `I_K → C_K`.

In particular, the local product is trivial on every principal idele.
The global Artin map therefore descends to the idele class group, where
it is the canonical surjective reciprocity homomorphism and has the
genuine idele-class norm range as its kernel.
-/

open scoped NumberField Classical BigOperators IsMulCommutative
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup


namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Pulling the canonical global norm-residue homomorphism back from
idele classes to ideles gives exactly the product of the chosen local
Artin homomorphisms. -/
theorem
    globalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin :
    (globalNormResidueMonoidHom K L).comp
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)) =
      globalArtinMonoidHom (K := K) (L := L) := by
  apply MonoidHom.ext
  intro a
  let a₀ :=
    artinFiniteSupportApproximation
      (K := K) (L := L) a
  have hnormApprox :
      globalNormResidueMonoidHom K L
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a) =
        globalNormResidueMonoidHom K L
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a₀) := by
    rw [globalNormResidueMonoidHom_apply,
      globalNormResidueMonoidHom_apply]
    change
      Additive.toMul
          (globalNormResidueEquiv K L
            (Additive.ofMul
              (globalNormClassFromIdele K L a))) =
        Additive.toMul
          (globalNormResidueEquiv K L
            (Additive.ofMul
              (globalNormClassFromIdele K L a₀)))
    exact
      congrArg
        (fun q =>
          Additive.toMul
            (globalNormResidueEquiv K L
              (Additive.ofMul q)))
        (by
          simpa only [a₀] using
            (globalNormClassFromIdele_eq_artinFiniteSupportApproximation
              (K := K) (L := L) a))
  calc
    globalNormResidueMonoidHom K L
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
        globalNormResidueMonoidHom K L
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a₀) :=
      hnormApprox
    _ =
        globalArtinMonoidHom
          (K := K) (L := L) a₀ := by
      dsimp only [a₀]
      rw [artinFiniteSupportApproximation]
      simp only [map_mul, map_prod]
      apply congrArg₂ (· * ·)
      · apply Finset.prod_congr rfl
        intro v _
        change
          globalNormResidueMonoidHom K L
              (IdeleGroup.infinitePlaceIdeleClass v
                (IdeleGroup.infiniteComponent v a)) =
            globalArtinMonoidHom
              (K := K) (L := L)
              (infinitePlaceIdele v
                (IdeleGroup.infiniteComponent v a))
        rw [globalArtinMonoidHom_infinitePlaceIdele]
        exact
          DFunLike.congr_fun
            (globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass
              (K := K) (L := L) v)
            (IdeleGroup.infiniteComponent v a)
      · apply Finset.prod_congr rfl
        intro v _
        change
          globalNormResidueMonoidHom K L
              (IdeleGroup.finitePlaceIdeleClass v.1
                (IdeleGroup.finiteComponent v.1 a)) =
            globalArtinMonoidHom
              (K := K) (L := L)
              (finitePlaceIdele v.1
                (IdeleGroup.finiteComponent v.1 a))
        rw [globalArtinMonoidHom_finitePlaceIdele]
        exact
          DFunLike.congr_fun
            (globalNormResidueMonoidHom_comp_finitePlaceIdeleClass
              (K := K) (L := L) v.1)
            (IdeleGroup.finiteComponent v.1 a)
    _ =
        globalArtinMonoidHom
          (K := K) (L := L) a :=
      (globalArtinMonoidHom_eq_artinFiniteSupportApproximation
        (K := K) (L := L) a).symm

/-- The chosen local Artin product is trivial on every principal
idele.  This is the global Artin product formula with the arithmetic
Frobenius normalization used by the local maps. -/
@[simp]
theorem globalArtinMonoidHom_principalIdele
    (x : Kˣ) :
    globalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.principalIdele K x) =
      1 := by
  rw [← DFunLike.congr_fun
    (globalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin
      (K := K) (L := L))
    (IdeleGroup.principalIdele K x)]
  change
    globalNormResidueMonoidHom K L
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (IdeleGroup.principalIdele K x)) =
      1
  have hclass :
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (IdeleGroup.principalIdele K x) =
        1 :=
    (QuotientGroup.eq_one_iff
      (IdeleGroup.principalIdele K x)).2
      ⟨x, rfl⟩
  rw [hclass, map_one]

/-- Expanded form of the global product formula: the product of all
chosen infinite local symbols and the finite-support product of all
chosen finite local symbols of a principal idele is one. -/
theorem chosenLocalArtin_product_principalIdele
    (x : Kˣ) :
    (∏ v : InfinitePlace K,
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.infiniteComponent v
            (IdeleGroup.principalIdele K x))) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.finiteComponent v
            (IdeleGroup.principalIdele K x)) =
      1 := by
  rw [← globalArtinMonoidHom_apply]
  simp
