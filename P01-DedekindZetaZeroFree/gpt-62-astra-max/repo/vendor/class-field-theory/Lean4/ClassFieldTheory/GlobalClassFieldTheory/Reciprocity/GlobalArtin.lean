module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleArtin
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfinitePlaceArtin
public import ClassFieldTheory.GlobalClassFieldTheory.Cohomology.CofinitelySplitFiniteExtension
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# The preliminary global Artin homomorphism

For a finite abelian extension `L / K`, the global norm-residue symbol
on ideles is the product of its archimedean and finite-place local
Artin factors.
-/

open scoped BigOperators Classical IsMulCommutative NumberField
  NumberField.LiesOver
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The preliminary global Artin homomorphism
`[·, L / K] : I_K → Gal(L / K)`, defined as the product of all local
Artin homomorphisms. -/
noncomputable def globalArtinMonoidHom :
    IdeleGroup K →* (L ≃ₐ[K] L) :=
  infinitePlaceGlobalArtinMonoidHom
      (K := K) (L := L) *
    finitePlaceGlobalArtinMonoidHom
      (K := K) (L := L)

/-- The preliminary global Artin homomorphism is continuous. -/
theorem globalArtinMonoidHom_continuous :
    Continuous
      (globalArtinMonoidHom
        (K := K) (L := L)) :=
  (infinitePlaceGlobalArtinMonoidHom_continuous
    (K := K) (L := L)).mul
      (finitePlaceGlobalArtinMonoidHom_continuous)

/-- The preliminary global Artin symbol is the product of its actual
archimedean and finite local factors. -/
theorem globalArtinMonoidHom_apply
    (a : IdeleGroup K) :
    globalArtinMonoidHom (L := L) a =
      (∏ v : InfinitePlace K,
        chosenInfinitePlaceArtinMonoidHom (L := L) v
          (IdeleGroup.infiniteComponent v a)) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        chosenFinitePlaceArtinMonoidHom (L := L) v
          (IdeleGroup.finiteComponent v a) := by
  change
    infinitePlaceGlobalArtinMonoidHom
            a *
        finitePlaceGlobalArtinMonoidHom
            a = _
  unfold infinitePlaceGlobalArtinMonoidHom
  rw [MonoidHom.finsetProd_apply]
  rfl

/-- The preliminary global Artin homomorphism of `L / K` kills every
actual relative-idele norm from `L`.  At each finite and infinite place
this is exactly the corresponding local reciprocity kernel theorem. -/
@[simp]
theorem globalArtinMonoidHom_relativeIdeleNorm_eq_one
    (z : RelativeIdeleGroup K L) :
    globalArtinMonoidHom (L := L)
        (RelativeIdeleGroup.norm K L z) =
      1 := by
  rw [globalArtinMonoidHom_apply]
  have hinfinite :
      (∏ v : InfinitePlace K,
        chosenInfinitePlaceArtinMonoidHom (L := L) v
          (IdeleGroup.infiniteComponent v
            (RelativeIdeleGroup.norm K L z))) =
        1 := by
    apply Finset.prod_eq_one
    intro v _
    apply MonoidHom.mem_ker.mp
    rw [chosenInfinitePlaceArtinMonoidHom_ker
        v]
    exact
      _root_.infiniteComponent_mem_infiniteTensorNormSubgroup_of_mem_relativeNorm_range

          (RelativeIdeleGroup.norm K L z) (⟨z, rfl⟩) v
  have hfinite :
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        chosenFinitePlaceArtinMonoidHom (L := L) v
          (IdeleGroup.finiteComponent v
            (RelativeIdeleGroup.norm K L z))) =
        1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    apply MonoidHom.mem_ker.mp
    rw [chosenFinitePlaceArtinMonoidHom_ker
        v]
    exact
      _root_.relativeIdeleNorm_finiteComponent_mem_chosenLocalNormSubgroup
            v z
  rw [hinfinite, hfinite, mul_one]

/-- The preliminary global Artin homomorphism kills the ordinary idele
norm `N_{L/K} : I_L → I_K`.  This is the relative-idele kernel theorem
above, transported by the canonical scalar-extension equivalence used in
the definition of `IdeleGroup.norm`. -/
@[simp]
theorem globalArtinMonoidHom_ideleNorm_eq_one
    (a : IdeleGroup L) :
    globalArtinMonoidHom (L := L)
        (IdeleGroup.norm K L a) =
      1 := by
  change
    globalArtinMonoidHom

        (RelativeIdeleGroup.norm K L
          ((relativeIdeleBaseChangeMulEquiv
             ).symm a)) =
      1
  exact
    globalArtinMonoidHom_relativeIdeleNorm_eq_one

      ((relativeIdeleBaseChangeMulEquiv
         ).symm a)

/-- Norm--restriction for the actual global Artin homomorphism.  In a number-field
diamond `K ⊂ K'`, `L ⊂ L'`, the ordinary idele norm and mathlib's standard
restriction composite form a commuting square. -/
theorem globalArtinMonoidHom_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L'] :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (globalArtinMonoidHom
          (K := K') (L := L')) =
      (globalArtinMonoidHom
        (K := K) (L := L)).comp
        (IdeleGroup.norm K K') := by
  apply MonoidHom.ext
  intro a
  change
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (infinitePlaceGlobalArtinMonoidHom (L := L') a *
          finitePlaceGlobalArtinMonoidHom (L := L') a) =
      infinitePlaceGlobalArtinMonoidHom (L := L)
          (IdeleGroup.norm K K' a) *
        finitePlaceGlobalArtinMonoidHom (L := L)
          (IdeleGroup.norm K K' a)
  rw [map_mul]
  have hinfinite :
      ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
          (infinitePlaceGlobalArtinMonoidHom (L := L') a) =
        infinitePlaceGlobalArtinMonoidHom (L := L)
          (IdeleGroup.norm K K' a) := by
    simpa only [MonoidHom.comp_apply] using
      DFunLike.congr_fun
        (infinitePlaceGlobalArtinMonoidHom_norm_restriction
          (K := K) (L := L))
        a
  have hfinite :
      ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
          (finitePlaceGlobalArtinMonoidHom (L := L') a) =
        finitePlaceGlobalArtinMonoidHom (L := L)
          (IdeleGroup.norm K K' a) := by
    simpa only [MonoidHom.comp_apply] using
      DFunLike.congr_fun
        (finitePlaceGlobalArtinMonoidHom_norm_restriction
          (K := K) (L := L))
        a
  rw [hinfinite, hfinite]

/-- For an abelian tower with fixed base field, the global Artin map
commutes with the genuine restriction homomorphism. -/
theorem globalArtinMonoidHom_restrict_tower
    {E : Type}
    [Field E] [NumberField E]
    [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [IsAbelianGalois K E] :
    (AlgEquiv.restrictNormalHom E).comp
        (globalArtinMonoidHom
          (K := K) (L := L)) =
      globalArtinMonoidHom
        (K := K) (L := E) := by
  apply MonoidHom.ext
  intro a
  change
    AlgEquiv.restrictNormalHom E
        (infinitePlaceGlobalArtinMonoidHom (L := L) a *
          finitePlaceGlobalArtinMonoidHom (L := L) a) =
      infinitePlaceGlobalArtinMonoidHom (L := E) a *
        finitePlaceGlobalArtinMonoidHom (L := E) a
  rw [map_mul]
  congr 1
  · simp only [infinitePlaceGlobalArtinMonoidHom,
      MonoidHom.finsetProd_apply, MonoidHom.comp_apply]
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro v _
    exact DFunLike.congr_fun
      (chosenInfinitePlaceArtinMonoidHom_restrict_tower (L := L) (E := E) v)
      (IdeleGroup.infiniteComponent v a)
  · change
      AlgEquiv.restrictNormalHom E
          (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            chosenFinitePlaceArtinMonoidHom (L := L) v
              (IdeleGroup.finiteComponent v a)) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          chosenFinitePlaceArtinMonoidHom (L := E) v
            (IdeleGroup.finiteComponent v a)
    rw [MonoidHom.map_finprod
      (AlgEquiv.restrictNormalHom E)
      (finitePlaceArtinFactors_hasFiniteMulSupport
        (K := K) (L := L) a)]
    apply finprod_congr
    intro v
    exact DFunLike.congr_fun
      (chosenFinitePlaceArtinMonoidHom_restrict_tower
        (K := K) (L := L) (E := E) v)
      (IdeleGroup.finiteComponent v a)

/-- The global Artin symbol of an archimedean one-place idele is its
local infinite-place Artin symbol. -/
@[simp]
theorem globalArtinMonoidHom_infinitePlaceIdele
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    globalArtinMonoidHom (L := L)
        (infinitePlaceIdele v x) =
      chosenInfinitePlaceArtinMonoidHom (L := L) v x := by
  classical
  change
    infinitePlaceGlobalArtinMonoidHom
            (infinitePlaceIdele v x) *
        finitePlaceGlobalArtinMonoidHom
            (infinitePlaceIdele v x) =
      chosenInfinitePlaceArtinMonoidHom
          v x
  have hinfinite :
      infinitePlaceGlobalArtinMonoidHom (L := L) (infinitePlaceIdele v x) =
        chosenInfinitePlaceArtinMonoidHom (L := L) v x := by
    unfold infinitePlaceGlobalArtinMonoidHom
    rw [MonoidHom.finsetProd_apply, Finset.prod_eq_single v]
    · rw [MonoidHom.comp_apply,
        infinitePlaceIdele_infiniteComponent_same]
    · intro w _ hwv
      rw [MonoidHom.comp_apply,
        infinitePlaceIdele_infiniteComponent_of_ne v w x hwv,
        map_one]
    · intro hv
      exact (hv (Finset.mem_univ v)).elim
  have hfinite :
      finitePlaceGlobalArtinMonoidHom (L := L) (infinitePlaceIdele v x) =
        1 := by
    change
      (∏ᶠ w : HeightOneSpectrum (𝓞 K),
        chosenFinitePlaceArtinMonoidHom
            w
          (IdeleGroup.finiteComponent w
            (infinitePlaceIdele v x))) = 1
    apply finprod_eq_one_of_forall_eq_one
    intro w
    rw [infinitePlaceIdele_finiteComponent, map_one]
  rw [hinfinite, hfinite, mul_one]

/-- The global Artin symbol of a finite one-place idele is its local
finite-place Artin symbol. -/
@[simp]
theorem globalArtinMonoidHom_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    globalArtinMonoidHom (L := L)
        (finitePlaceIdele v x) =
      chosenFinitePlaceArtinMonoidHom (L := L) v x := by
  change
    infinitePlaceGlobalArtinMonoidHom
            (finitePlaceIdele v x) *
        finitePlaceGlobalArtinMonoidHom
            (finitePlaceIdele v x) =
      chosenFinitePlaceArtinMonoidHom
          v x
  rw [infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele,
    finitePlaceGlobalArtinMonoidHom_finitePlaceIdele, one_mul]

/-- Every chosen finite-place decomposition group is contained in the
image of the global Artin homomorphism. -/
theorem finitePlaceDecompositionGroup_le_globalArtinMonoidHom_range
    (v : HeightOneSpectrum (𝓞 K)) :
    finitePlaceDecompositionGroup (L := L) v ≤
      (globalArtinMonoidHom
        (K := K) (L := L)).range := by
  rw [← chosenFinitePlaceArtinMonoidHom_range
      v]
  intro σ hσ
  rcases hσ with ⟨x, rfl⟩
  exact
    ⟨finitePlaceIdele v x,
      globalArtinMonoidHom_finitePlaceIdele
          v x⟩

/-- The actual global Artin homomorphism of a finite abelian extension
of number fields is surjective. -/
theorem globalArtinMonoidHom_surjective :
    Function.Surjective
      (globalArtinMonoidHom
        (K := K) (L := L)) := by
  let H : Subgroup (L ≃ₐ[K] L) :=
    (globalArtinMonoidHom
      (K := K) (L := L)).range
  let :=
    H.normal_of_isMulCommutative
  let E :=
    IntermediateField.fixedField H
  let : IsGalois K E := by
    dsimp only [E]
    infer_instance
  have hsplit :
      ∀ v : HeightOneSpectrum (𝓞 K),
        FinitePlaceSplitsCompletely (L := E) v := by
    intro v
    apply
      _root_.finitePlaceSplitsCompletely_of_decompositionGroup_le_restrictNormalHom_ker (E := E) (N := L) v
    rw [IntermediateField.restrictNormalHom_ker]
    change
      finitePlaceDecompositionGroup
            v ≤
        (IntermediateField.fixedField H).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_fixedField]
    simpa only [H] using
      finitePlaceDecompositionGroup_le_globalArtinMonoidHom_range (L := L) v
  have hfinite :
      {v : HeightOneSpectrum (𝓞 K) |
        ¬ FinitePlaceSplitsCompletelyInExtension (E := E) v}.Finite := by
    apply Set.finite_empty.subset
    intro v hv
    exact
      (hv
        ((_root_.finitePlaceSplitsCompletely_iff_inExtension
            v).mp
            (hsplit v))).elim
  have hHtop :
      H = (⊤ : Subgroup (L ≃ₐ[K] L)) := by
    calc
      H =
          (IntermediateField.fixedField H).fixingSubgroup :=
        (IntermediateField.fixingSubgroup_fixedField H).symm
      _ = E.fixingSubgroup := rfl
      _ = (⊥ : IntermediateField K L).fixingSubgroup :=
        congrArg
          (fun F : IntermediateField K L =>
            F.fixingSubgroup)
          (IntermediateField.finrank_eq_one_iff.mp (Cohomology.finrank_eq_one_of_finite_nonSplittingPlaces
            K E hfinite))
      _ = ⊤ := by
        rw [IntermediateField.fixingSubgroup_bot]
  apply MonoidHom.range_eq_top.mp
  simpa using hHtop

end Reciprocity
end GlobalClassFieldTheory

end
