module

public import ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.RingTheory.ClassGroup.ExtendedHom

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Extension of ideles and ideal classes

For a finite Galois extension of number fields, scalar extension of the
relative adele algebra followed by the relative-to-ordinary comparison
gives the usual extension map on ideles.  This file descends that map to
idele classes and compares it with extension of fractional ideals and
ideal classes.
-/

open scoped NumberField TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v w

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [IsGalois K L] in
/-- On a base-field local unit, the finite relative-to-ordinary
comparison is the canonical map to the chosen place above it. -/
theorem finitePlaceTensorUnitsEquivAboveAdic_localIdeleInclusion
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : (w.adicCompletion K)ˣ) :
    finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w
        (localIdeleInclusion
          (K := K) (L := L) w x) W =
      Units.map
        (finitePlaceAdicCompletionMap K L w W).toMonoidHom
        x := by
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [finitePlaceTensorUnitsEquivAboveAdic_apply_extension]
  apply Units.ext
  simp only [Units.coe_map, Units.coe_mapEquiv,
    finitePlaceLocalTensorDecompositionUnitsComponent_coe,
    localIdeleInclusion]
  change
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w a
        (finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w a
          ((x : w.adicCompletion K) ⊗ₜ[K] 1)) =
      finitePlaceAdicCompletionMap K L w
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a)
        (x : w.adicCompletion K)
  rw [finitePlaceLocalTensorDecompositionComponent_tmul]
  simp only [map_one, mul_one]
  exact
    finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
      K L w a (x : w.adicCompletion K)

namespace FractionalIdealGroup

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Extension of nonzero fractional ideals along the inclusion of number
fields. -/
def extension :
    FractionalIdealGroup K →* FractionalIdealGroup L :=
  Units.map
    (FractionalIdeal.extendedHom L (𝓞 L)).toMonoidHom

end FractionalIdealGroup

namespace ClassGroup
end ClassGroup

namespace IdeleGroup

/-- The usual extension map on ideles, constructed through the relative
tensor-product presentation. -/
def extension :
    IdeleGroup K →* IdeleGroup L :=
  relativeIdeleBaseChangeMulEquiv.toMonoidHom.comp
    (RelativeIdeleGroup.inclusion K L)

omit [IsGalois K L] in
theorem extension_infiniteComponent
    (a : IdeleGroup K)
    (W : InfinitePlace L) :
    infiniteComponent W (extension K L a) =
      letI : Algebra.IsIntegral K L :=
        Algebra.IsIntegral.of_finite K L
      let v :=
        _root_.infinitePlaceBelow (K := K) W
      letI : W.1.LiesOver v.1 := ⟨rfl⟩
      Units.map
        (NumberField.LiesOver.completionMap
          (v := v) (w := W))
        (infiniteComponent v a) := by
  let : Algebra.IsIntegral K L :=
    Algebra.IsIntegral.of_finite K L
  let : Algebra.IsSeparable K L :=
    Algebra.IsSeparable.of_integral K L
  let v :=
    _root_.infinitePlaceBelow (K := K) W
  let : W.1.LiesOver v.1 := ⟨rfl⟩
  apply Units.ext
  change
    (ContinuousMulEquiv.piUnits (extension K L a).1 W :
      W.Completion) = _
  change
    (ContinuousMulEquiv.piUnits
      (_root_.relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.inclusion K L a)).1 W :
      W.Completion) = _
  rw [_root_.relativeIdeleBaseChangeMulEquiv_infinite]
  let f :=
    _root_.relativeInfiniteTensorPiMulEquiv
      (K := K) (L := L)
      ((_root_.relativeIdeleToLocalData
        (K := K) (L := L)
        (RelativeIdeleGroup.inclusion K L a)).infinite)
  change
    (ContinuousMulEquiv.piUnits
      (ContinuousMulEquiv.piUnits.symm f) W :
      W.Completion) = _
  rw [ContinuousMulEquiv.piUnits.apply_symm_apply]
  dsimp only [f]
  rw [_root_.relativeInfiniteTensorPiMulEquiv_apply]
  simp only [_root_.relativeIdeleToLocalData]
  rw [RelativeIdeleGroup.infiniteComponent_inclusion]
  rw [_root_.infinitePlaceTensorUnitsEquivAbove_apply]
  simp only [Units.coe_map]
  change
    _root_.infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) v
        ((infiniteComponent v a : v.Completion) ⊗ₜ[K] (1 : L))
        ⟨W, rfl⟩ =
      NumberField.LiesOver.completionMap
        (v := v) (w := W)
        (infiniteComponent v a : v.Completion)
  simpa only [map_one, mul_one] using
    (_root_.infinitePlaceTensorRingEquivAbove_tmul
      (K := K) (L := L) v ⟨W, rfl⟩
      (infiniteComponent v a : v.Completion) (1 : L))

omit [IsGalois K L] in
/-- The finite component of an extended idele is the canonical local
completion map applied to the component below it. -/
@[simp]
theorem extension_finiteComponent
    (a : IdeleGroup K)
    (W : HeightOneSpectrum (𝓞 L)) :
    finiteComponent W (extension K L a) =
      Units.map
        (finitePlaceAdicCompletionMap K L
          (_root_.finitePlaceBelow (K := K) W)
          ⟨W, rfl⟩).toMonoidHom
        (finiteComponent
          (_root_.finitePlaceBelow (K := K) W) a) := by
  change (extension K L a).2 W = _
  rw [extension, MonoidHom.comp_apply]
  change
    (relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)
      (RelativeIdeleGroup.inclusion K L a)).2 W = _
  rw [
    relativeIdeleBaseChangeMulEquiv_finite,
    _root_.relativeFiniteIdeleToFiniteIdele_apply,
    _root_.relativeFiniteTensorPiMulEquiv_apply]
  change
    _root_.finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L)
        (_root_.finitePlaceBelow (K := K) W)
        ((_root_.relativeIdeleToLocalData
          (K := K) (L := L)
          (RelativeIdeleGroup.inclusion K L a)).finite
            (_root_.finitePlaceBelow (K := K) W))
        ⟨W, rfl⟩ =
      _
  simp only [_root_.relativeIdeleToLocalData]
  rw [RelativeIdeleGroup.finiteComponent_inclusion,
    _root_.finitePlaceTensorUnitsEquivAboveAdic_localIdeleInclusion]

omit [IsGalois K L] in
/-- Extension of a principal idele is the corresponding principal idele
of the extension field. -/
@[simp]
theorem extension_principalIdele (x : Kˣ) :
    extension K L (principalIdele K x) =
      principalIdele L
        (Units.map (algebraMap K L).toMonoidHom x) := by
  rw [extension, MonoidHom.comp_apply,
    RelativeIdeleGroup.inclusion_principalIdele]
  apply Prod.ext
  · apply Units.ext
    funext W
    change
      _root_.infinitePlaceTensorUnitsEquivAbove
          (K := K) (L := L)
          (_root_.infinitePlaceBelow (K := K) W)
          ((_root_.relativeIdeleToLocalData
            (K := K) (L := L)
            (RelativeIdeleGroup.principalIdele K L
              (Units.map (algebraMap K L).toMonoidHom x))).infinite
              (_root_.infinitePlaceBelow (K := K) W))
          ⟨W, rfl⟩ =
        algebraMap L W.Completion
          (algebraMap K L (x : K))
    simp only [_root_.relativeIdeleToLocalData]
    rw [RelativeIdeleGroup.infiniteComponent_principalIdele]
    rw [
      _root_.infinitePlaceTensorUnitsEquivAbove_localFieldIdeleInclusion]
    simp
  · change
      (relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.principalIdele K L
          (Units.map (algebraMap K L).toMonoidHom x))).2 =
        (principalIdele L
          (Units.map (algebraMap K L).toMonoidHom x)).2
    rw [relativeIdeleBaseChangeMulEquiv_finite]
    apply RestrictedProduct.ext
    intro W
    rw [_root_.relativeFiniteIdeleToFiniteIdele_apply,
      _root_.relativeFiniteTensorPiMulEquiv_apply]
    change
      _root_.finitePlaceTensorUnitsEquivAboveAdic
          (K := K) (L := L)
          (_root_.finitePlaceBelow (K := K) W)
          ((_root_.relativeIdeleToLocalData
            (K := K) (L := L)
            (RelativeIdeleGroup.principalIdele K L
              (Units.map (algebraMap K L).toMonoidHom x))).finite
              (_root_.finitePlaceBelow (K := K) W))
          ⟨W, rfl⟩ =
        Units.map (FinitePlace.embedding (K := L) W)
          (Units.map (algebraMap K L).toMonoidHom x)
    simp only [_root_.relativeIdeleToLocalData]
    rw [RelativeIdeleGroup.finiteComponent_principalIdele]
    rw [
      _root_.finitePlaceTensorUnitsEquivAboveAdic_localFieldIdeleInclusion]

end IdeleGroup

/-- The usual extension map on idele classes. -/
def ideleClassExtension :
    IdeleClassGroup K →* IdeleClassGroup L :=
  QuotientGroup.map
    (IdeleGroup.principalSubgroup K)
    (IdeleGroup.principalSubgroup L)
    (IdeleGroup.extension K L)
    (by
      rintro _ ⟨x, rfl⟩
      exact
        ⟨Units.map (algebraMap K L).toMonoidHom x,
          (IdeleGroup.extension_principalIdele K L x).symm⟩)

omit [IsGalois K L] in
@[simp]
theorem ideleClassExtension_mk (a : IdeleGroup K) :
    ideleClassExtension K L
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (IdeleGroup.extension K L a) :=
  rfl
