module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.InfinitePlaceTensorNorm
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Small Hilbert norm subgroups and everywhere-unramified extensions

For a finite Galois extension which is unramified at both finite and
infinite places, every idele integral at all finite places is an actual
relative-idele norm.  It follows that the actual idele-class norm range
contains the small-Hilbert norm subgroup.

This realizes the maximality of the small Hilbert class field on the
norm-subgroup side.  The resulting quotient transition gives a canonical
surjection from the ordinary class group, its exact kernel
factorization, and the divisibility of the extension norm quotient order
by the class number.
-/

open scoped IsMulCommutative NumberField NumberField.LiesOver

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Keep norm-range quotient normality out of exported declaration types. -/
local instance
    smallHilbertNormCharacterization_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

omit [FiniteDimensional K L] in
/-- At an extension unramified at all infinite places, the determinant
norm image of every infinite tensor factor is the whole local
multiplicative group. -/
theorem
    infiniteTensorNormSubgroup_eq_top_of_isUnramifiedAtInfinitePlaces
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (v : InfinitePlace K) :
    _root_.infiniteTensorNormSubgroup
        (K := K) (L := L) v = ⊤ := by
  obtain ⟨w, hw⟩ :=
    InfinitePlace.comap_surjective
      (K := L) v
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  rw [
    _root_.infiniteTensorNormSubgroup_eq_localNormSubgroup
      (K := K) (L := L) v w hw]
  apply top_unique
  intro x _
  refine
    ⟨Units.map
        (algebraMap
          v.Completion w.Completion).toMonoidHom x,
      ?_⟩
  apply Units.ext
  change
    Algebra.norm v.Completion
        (algebraMap v.Completion w.Completion
          (x : v.Completion)) =
      (x : v.Completion)
  rw [
    Algebra.norm_algebraMap,
    InfinitePlace.IsUnramified.finrank_eq_one
      v (w.isUnramified K),
    pow_one]

/-- If the finite ramification support is empty, the chosen completion
above every finite base place is unramified. -/
theorem chosenFinitePlaceIsUnramified_of_no_ramifiedFinitePlaces
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (v : HeightOneSpectrum (𝓞 K)) :
    _root_.ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  apply
    _root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := L) v
  by_contra hramified
  have hv :
      v ∈ _root_.ramifiedBaseFinitePlaces
        (K := K) (L := L) := by
    rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
    exact
      ⟨_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v),
        _root_.finitePlaceExtensionCentre_liesOver
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v),
        hramified⟩
  rw [hunramifiedFinite] at hv
  simp at hv

/-- In an extension unramified at every finite and infinite place,
every idele integral at all finite places is an actual relative-idele
norm. -/
theorem
    integralAtFinitePlaces_le_relativeIdeleNorm_range_of_everywhereUnramified
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    IdeleGroup.integralAtFinitePlaces (K := K) ≤
      (RelativeIdeleGroup.norm K L).range := by
  intro a ha
  refine
    (_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms
      (K := K) (L := L) a).2 ⟨?_, ?_⟩
  · intro v
    rw [
      infiniteTensorNormSubgroup_eq_top_of_isUnramifiedAtInfinitePlaces
        (K := K) (L := L) v]
    exact Subgroup.mem_top _
  · intro v
    rw [
      _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
    apply
      _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v
        (chosenFinitePlaceIsUnramified_of_no_ramifiedFinitePlaces
          (K := K) (L := L) hunramifiedFinite v)
    change a.2 v ∈ (v.adicCompletionIntegers K).units
    exact
      (FiniteIdeleGroup.mem_integralSubgroup_iff a.2).1 ha v

private theorem integralIdeleClass_mem_ideleClassNorm_range_of_everywhereUnramified
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    {a : IdeleGroup K}
    (ha : a ∈ IdeleGroup.integralAtFinitePlaces (K := K)) :
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a ∈
      (_root_.ideleClassNorm K L).range := by
  obtain ⟨z, hz⟩ :=
    integralAtFinitePlaces_le_relativeIdeleNorm_range_of_everywhereUnramified
      (K := K) (L := L) hunramifiedFinite ha
  refine
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (_root_.relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z),
      ?_⟩
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.norm K L
          (_root_.relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L) z)) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a
  rw [IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv, hz]

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem principalIdeleClass_mem_ideleClassNorm_range
    {a : IdeleGroup K}
    (ha : a ∈ IdeleGroup.principalSubgroup K) :
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a ∈
      (_root_.ideleClassNorm K L).range := by
  have haOne :
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a = 1 :=
    (QuotientGroup.eq_one_iff a).2 ha
  rw [haOne]
  exact ((_root_.ideleClassNorm K L).range).one_mem

/-- The norm subgroup of an everywhere-unramified finite Galois
extension contains the small-Hilbert norm subgroup. -/
theorem
    smallHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_everywhereUnramified
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    smallHilbertClassFieldNormSubgroup (K := K) ≤
      (_root_.ideleClassNorm K L).range := by
  rw [smallHilbertClassFieldNormSubgroup,
    Subgroup.map_le_iff_le_comap]
  apply sup_le
  · intro a ha
    exact
      integralIdeleClass_mem_ideleClassNorm_range_of_everywhereUnramified
        (K := K) (L := L) hunramifiedFinite ha
  · intro a ha
    exact
      principalIdeleClass_mem_ideleClassNorm_range
        (K := K) (L := L) ha

/-- The canonical transition from the small-Hilbert reciprocity
quotient to the actual norm quotient of an everywhere-unramified
extension. -/
def smallHilbertClassFieldQuotientToIdeleClassNormQuotient
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    (IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K)) →*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  QuotientGroup.map
    (smallHilbertClassFieldNormSubgroup (K := K))
    ((_root_.ideleClassNorm K L).range)
    (MonoidHom.id _)
    (fun _ hx =>
      smallHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_everywhereUnramified
        (K := K) (L := L) hunramifiedFinite hx)

/-- The small-Hilbert quotient transition sends an idele class to the
same class modulo the actual norm subgroup. -/
@[simp]
theorem smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (x : IdeleClassGroup K) :
    smallHilbertClassFieldQuotientToIdeleClassNormQuotient
        (K := K) (L := L) hunramifiedFinite
        (QuotientGroup.mk'
          (smallHilbertClassFieldNormSubgroup (K := K)) x) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K L).range) x :=
  rfl



















end GlobalClassFields
end GlobalClassFieldTheory

end
