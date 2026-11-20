module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorRamification
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianLocalConductorComparison
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorInfinitePart
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertNormCharacterization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteLocalGlobalArtinCompatibility
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.SeparableClosurePadicLift
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicCyclicData
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicAuxiliaryField
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Exact finite ramification loci for abelian norm data

For a finite abelian extension, the modulus constructed from the
actual chosen local norm groups has support exactly the ramified finite
places.  At the archimedean places, the determinant-norm image is the
whole local multiplicative group exactly when the extension is
unramified at infinity.

The finite statement is deliberately about the locally constructed
norm modulus.  Identifying it with the minimal narrow finite conductor also
requires the compatibility between the actual global norm-residue map
and the chosen local Artin map on one-place ideles.
-/

open scoped NumberField Classical NumberField.LiesOver

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open LocalClassFieldTheory LocalFieldTheory
open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

private theorem
    finitePlaceIdeleClass_mem_normRange_of_mem_narrowFiniteHigherUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (hx :
      x ∈ RayClass.localHigherUnitGroup v
        (ideleClassNormNarrowFiniteConductor
          (K := K) (L := L) v)) :
    IdeleGroup.finitePlaceIdeleClass v x ∈
      (_root_.ideleClassNorm K L).range := by
  apply
    ideleClassNorm_narrowFiniteConductor_isDefiningModulus

  apply
    RayClass.localHigherUnitClassSubgroup_le_congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormNarrowFiniteConductor
           )) v
  refine ⟨x, ?_, rfl⟩
  change
    x ∈ RayClass.localHigherUnitGroup v
      (ideleClassNormNarrowFiniteConductor
          v)
  exact hx

private theorem
    narrowFiniteHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.localHigherUnitGroup v
        (ideleClassNormNarrowFiniteConductor
          (K := K) (L := L) v) ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  intro x hx
  apply
    (Reciprocity.chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm
        v x).1
  have hglobal :=
    (Reciprocity.globalNormResidueMonoidHom_eq_one_iff
      K L (IdeleGroup.finitePlaceIdeleClass v x)).2
      ((by
        apply
          ideleClassNorm_narrowFiniteConductor_isDefiningModulus

        apply
          RayClass.localHigherUnitClassSubgroup_le_congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                 )) v
        refine ⟨x, ?_, rfl⟩
        change
          x ∈ RayClass.localHigherUnitGroup v
            (ideleClassNormNarrowFiniteConductor
                v)
        exact hx))
  exact (DFunLike.congr_fun
    (Reciprocity.globalNormResidueMonoidHom_comp_finitePlaceIdeleClass
        v) x).symm.trans hglobal

/-- The modulus obtained from the actual chosen local norm groups is
bounded by the minimal narrow finite conductor.  The substantive input is the
finite-place local--global compatibility theorem: a one-place idele
class is a global class norm exactly when its local component is a norm
from the chosen completion. -/
theorem ideleClassNormDefiningModulus_le_narrowFiniteConductor :
    ideleClassNormDefiningModulus (K := K) (L := L) ≤
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) := ideleClassNormDefiningModulus_le_of_localHigherUnitGroup_le

      (ideleClassNormNarrowFiniteConductor)
      (narrowFiniteHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
         )

/-- The minimal narrow finite conductor of an actual finite abelian extension
is exactly the modulus obtained from its actual chosen local norm
groups. -/
theorem ideleClassNorm_narrowFiniteConductor_eq_normDefiningModulus :
    ideleClassNormNarrowFiniteConductor (K := K) (L := L) =
      ideleClassNormDefiningModulus (K := K) (L := L) :=
  le_antisymm
    (ideleClassNorm_narrowFiniteConductor_le_normDefiningModulus
      (K := K) (L := L))
    (ideleClassNormDefiningModulus_le_narrowFiniteConductor
      (K := K) (L := L))

/-- At every finite place, the corresponding exponent of the minimal
narrow finite conductor is exactly the local conductor exponent of the
genuine chosen localized extension.  Thus the narrow finite conductor is
the finite product of its actual local conductors, encoded pointwise in
`RayClass.Modulus`. -/
theorem
    ideleClassNorm_narrowFiniteConductor_apply_eq_chosenLocalConductorExponent
    (v : HeightOneSpectrum (𝓞 K)) :
    ideleClassNormNarrowFiniteConductor (K := K) (L := L) v =
      ideleClassNormChosenFinitePlaceLocalConductorExponent
        (K := K) (L := L) v := by
  calc
    ideleClassNormNarrowFiniteConductor v =
        ideleClassNormDefiningModulus v := by
      rw [ideleClassNorm_narrowFiniteConductor_eq_normDefiningModulus]
    _ =
        ideleClassNormLocalHigherUnitExponent
            v :=
      ideleClassNormDefiningModulus_apply
          v
    _ =
        ideleClassNormChosenFinitePlaceLocalConductorExponent
            v :=
      ideleClassNormLocalHigherUnitExponent_eq_localConductorExponent
          v

/-- For a finite abelian extension, the support of the modulus obtained
from the actual chosen local norm subgroups is precisely the set of
ramified finite places of the base field. -/
theorem
    ideleClassNormDefiningModulus_support_eq_ramifiedBaseFinitePlaces :
    (ideleClassNormDefiningModulus
        (K := K) (L := L)).support =
      _root_.ramifiedBaseFinitePlaces
        (K := K) (L := L) := by
  ext v
  rw [
    mem_ideleClassNormDefiningModulus_support_iff_not_chosenFinitePlaceIsUnramified,
    _root_.mem_ramifiedBaseFinitePlaces_iff]
  constructor
  · intro hramified
    let w :=
      _root_.chosenFinitePlaceExtension
        (L := L) v
    refine
      ⟨(_root_.finitePlaceExtensionCentre
        v w),
        _root_.finitePlaceExtensionCentre_liesOver
            v w, ?_⟩
    intro hW
    exact
      hramified
        (_root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
            v hW)
  · rintro ⟨P, hP, hP_ramified⟩ hchosen
    apply hP_ramified
    apply
      _root_.isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified
          v P
    · apply HeightOneSpectrum.ext
      exact hP.over.symm
    · exact hchosen

/-- The support of the minimal narrow finite conductor of a finite abelian
extension is exactly its finite ramification locus. -/
theorem
    ideleClassNorm_narrowFiniteConductor_support_eq_ramifiedBaseFinitePlaces :
    (ideleClassNormNarrowFiniteConductor
      (K := K) (L := L)).support =
      _root_.ramifiedBaseFinitePlaces
        (K := K) (L := L) := by
  rw [
    ideleClassNorm_narrowFiniteConductor_eq_normDefiningModulus,
    ideleClassNormDefiningModulus_support_eq_ramifiedBaseFinitePlaces]

omit [FiniteDimensional K L] in
/-- A ramified real-to-complex completion makes the corresponding
archimedean tensor norm subgroup proper. -/
private theorem infiniteTensorNormSubgroup_ne_top_of_isRamified
    (v : InfinitePlace K)
    (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (hramified : w.IsRamified K) :
    _root_.infiniteTensorNormSubgroup
      (K := K) (L := L) v ≠ ⊤ := by
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  rw [
    _root_.infiniteTensorNormSubgroup_eq_localNormSubgroup
        v w hw]
  have hvReal : v.IsReal := by
    rw [← hw]
    exact hramified.isReal
  let eRealField :=
    InfinitePlace.Completion.ringEquivRealOfIsReal
      hvReal
  let eRealUnits :=
    Units.mapEquiv eRealField.toMulEquiv
  let eComplexField :=
    InfinitePlace.Completion.ringEquivComplexOfIsComplex
      hramified.isComplex
  let eComplexUnits :=
    Units.mapEquiv eComplexField.toMulEquiv
  let :=
    InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
      w hvReal
  have hCompletionCompatible :
      RingHom.comp (algebraMap ℝ ℂ) eRealField =
        RingHom.comp eComplexField
          (algebraMap v.Completion w.Completion) := by
    ext x
    change
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal hvReal x : ℂ) =
        InfinitePlace.Completion.extensionEmbedding w
          ((algebraMap v.Completion w.Completion) x)
    rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    exact
      (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
        w (v := v)).symm
  have hCompletionCompatibleSymm :=
    LocalClassFieldTheory.ringEquiv_compat_symm
      eRealField eComplexField hCompletionCompatible
  have hRealComplexNormTransport :
      (localNormSubgroup ℝ ℂ).map
          eRealUnits.symm.toMonoidHom =
        localNormSubgroup
          v.Completion w.Completion := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine ⟨eComplexUnits.symm z, ?_⟩
      exact
        (LocalClassFieldTheory.normUnits_map_ringEquiv
          eRealField.symm eComplexField.symm
          hCompletionCompatibleSymm z).symm
    · rintro ⟨z, rfl⟩
      refine
        ⟨normUnits ℝ ℂ (eComplexUnits z),
          ⟨eComplexUnits z, rfl⟩, ?_⟩
      calc
        _ =
            normUnits v.Completion w.Completion
              (eComplexUnits.symm (eComplexUnits z)) := LocalClassFieldTheory.normUnits_map_ringEquiv
              eRealField.symm eComplexField.symm
              hCompletionCompatibleSymm
              (eComplexUnits z)
        _ = normUnits v.Completion w.Completion z := by
          rw [eComplexUnits.symm_apply_apply]
  have hNegativeOne :
      (-1 : ℝˣ) ∉ localNormSubgroup ℝ ℂ := by
    rw [
      ← LocalClassFieldTheory.realUnitsSign_ker_eq_complexNormSubgroup,
      LocalClassFieldTheory.mem_realUnitsSign_ker_iff]
    norm_num
  intro htop
  have hx :
      eRealUnits.symm (-1 : ℝˣ) ∈
        localNormSubgroup v.Completion w.Completion := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [← hRealComplexNormTransport] at hx
  obtain ⟨z, hz, hzEq⟩ := hx
  exact hNegativeOne ((eRealUnits.symm.injective hzEq) ▸ hz)

omit [FiniteDimensional K L] in
/-- At a base infinite place, the determinant-norm image is the whole
local multiplicative group exactly when the extension is unramified
above that place. -/
theorem infiniteTensorNormSubgroup_eq_top_iff_isUnramifiedIn
    (v : InfinitePlace K) :
    _root_.infiniteTensorNormSubgroup
          (K := K) (L := L) v = ⊤ ↔
      v.IsUnramifiedIn L := by
  obtain ⟨w, hw⟩ :=
    InfinitePlace.comap_surjective
      (K := L) v
  have hUnramified :
      v.IsUnramifiedIn L ↔ w.IsUnramified K := by
    rw [← hw, InfinitePlace.isUnramifiedIn_comap]
  rw [hUnramified]
  constructor
  · intro htop
    by_contra hramified
    exact
      (infiniteTensorNormSubgroup_ne_top_of_isRamified
          v w hw hramified)
        htop
  · intro hunramified
    let : w.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
    rw [
      _root_.infiniteTensorNormSubgroup_eq_localNormSubgroup
          v w hw]
    apply top_unique
    intro x _
    refine
      ⟨Units.map
          (algebraMap
            v.Completion w.Completion).toMonoidHom x, ?_⟩
    apply Units.ext
    change
      Algebra.norm v.Completion
          (algebraMap v.Completion w.Completion
            (x : v.Completion)) =
        (x : v.Completion)
    rw [
      Algebra.norm_algebraMap,
      InfinitePlace.IsUnramified.finrank_eq_one
        v hunramified,
      pow_one]

/-- The infinite part of the full conductor of an idèle-class norm range is
exactly the set of ramified real places. -/
theorem ideleClassNormFullConductor_infinitePart_eq_realRamificationLocus :
    (ideleClassNormConductorialSubgroup
        (K := K) (L := L)).fullConductor.infinitePart =
      (Finset.univ.filter fun v : RayClass.RealPlace K =>
        ¬ v.1.IsUnramifiedIn L) := by
  classical
  ext v
  change
    v ∈ (ideleClassNormConductorialSubgroup
         ).fullConductorInfinitePart ↔
      v ∈ (Finset.univ.filter fun w : RayClass.RealPlace K =>
        ¬ w.1.IsUnramifiedIn L)
  rw [ConductorialSubgroup.mem_fullConductorInfinitePart_iff,
    Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change
    (¬ (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤
        (_root_.ideleClassNorm K L).range) ↔
      ¬ v.1.IsUnramifiedIn L
  apply not_congr
  calc
    _ ≤
          (_root_.ideleClassNorm K L).range ↔
        _root_.infiniteTensorNormSubgroup
              v.1 = ⊤ := by
      constructor
      · intro hRange
        apply top_unique
        intro x _hx
        apply
          (Reciprocity.infinitePlaceIdeleClass_mem_ideleClassNorm_range_iff
              v.1 x).1
        exact hRange ⟨x, rfl⟩
      · intro hTop
        rintro _ ⟨x, rfl⟩
        apply
          (Reciprocity.infinitePlaceIdeleClass_mem_ideleClassNorm_range_iff
              v.1 x).2
        rw [hTop]
        exact Subgroup.mem_top x
    _ ↔ v.1.IsUnramifiedIn L :=
      infiniteTensorNormSubgroup_eq_top_iff_isUnramifiedIn
          v.1

end GlobalClassFields
end GlobalClassFieldTheory

namespace ClassFieldTheory

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The finite exponent of the full norm conductor is the local conductor
exponent at the chosen completion above the place. -/
theorem abelianFullConductor_finiteExponent_eq_localConductorExponent
    (v : HeightOneSpectrum (𝓞 K)) :
    (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
        (K := K) (L := L)).fullConductor.finitePart v =
      GlobalClassFieldTheory.GlobalClassFields.ideleClassNormChosenFinitePlaceLocalConductorExponent
        (K := K) (L := L) v := by
  change
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
          v = _
  exact
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_narrowFiniteConductor_apply_eq_chosenLocalConductorExponent
        v

end ClassFieldTheory

end
