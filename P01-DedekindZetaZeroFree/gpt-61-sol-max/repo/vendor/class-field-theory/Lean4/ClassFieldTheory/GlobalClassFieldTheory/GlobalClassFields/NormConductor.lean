module

public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.OnePlaceNormKernel
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorSupport
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorRayClassMaximality

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/










set_option autoImplicit false

/-!
# Narrow finite conductors of actual idele-class norm subgroups

For a finite Galois extension of number fields, the image of the
idele-class norm contains an explicitly constructed ray congruence
subgroup.  At a ramified finite place we choose a sufficiently deep
higher-unit group inside the open local norm subgroup.  Outside the
finite ramification set, the full local unit group already consists of
norms.  The archimedean positive subgroup is always contained in the
corresponding tensor-norm image.

This produces a defining modulus directly from the actual extension.  In
particular, the idele-class norm range is open, closed, and of finite
index.  Its narrow finite conductor can only be supported at ramified
finite places.  The full conductor, including an archimedean component,
is deliberately not defined here.
-/

open scoped NumberField Classical IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain Topology

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Fix the canonical commutative idèle-class structure used by the norm
quotients in this module. -/
local instance normConductorIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

omit [NumberField L] in
/-- Every chosen finite-place norm subgroup contains a local
higher-unit group.  This is the local source used to construct an
actual defining modulus. -/
theorem exists_localHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ,
      RayClass.localHigherUnitGroup v n ≤
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v := by
  have hnormOne :
      (1 : (v.adicCompletion K)ˣ) ∈
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v :=
    (_root_.chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v).one_mem
  have hnormNhds :
      (_root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v :
        Set (v.adicCompletion K)ˣ) ∈
        𝓝 (1 : (v.adicCompletion K)ˣ) :=
    (_root_.chosenFinitePlaceLocalNormSubgroup_isOpen
      (K := K) (L := L) v).mem_nhds hnormOne
  obtain ⟨n, hn⟩ :=
    RayClass.exists_localHigherUnitGroup_subset v hnormNhds
  exact ⟨n, fun _ hx => hn hx⟩

/-- The least higher-unit exponent whose group lies in the chosen
finite-place norm subgroup. -/
noncomputable def ideleClassNormLocalHigherUnitExponent
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.find
    (exists_localHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v)

omit [NumberField L] in
/-- The local higher-unit group at the selected exponent lies in the
chosen local norm subgroup. -/
theorem ideleClassNormLocalHigherUnitExponent_spec
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.localHigherUnitGroup v
        (ideleClassNormLocalHigherUnitExponent
          (K := K) (L := L) v) ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v :=
  Nat.find_spec
    (exists_localHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v)

omit [NumberField L] in
/-- The selected local higher-unit exponent is minimal among all
exponents whose higher-unit group lies in the chosen local norm
subgroup. -/
theorem ideleClassNormLocalHigherUnitExponent_min
    (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ}
    (hn :
      RayClass.localHigherUnitGroup v n ≤
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v) :
    ideleClassNormLocalHigherUnitExponent
        (K := K) (L := L) v ≤ n :=
  Nat.find_min'
    (exists_localHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v)
    hn

omit [NumberField L] in
/-- The selected local exponent is zero exactly when every integral unit
of the finite-place completion is a norm from the chosen localized
extension. -/
theorem ideleClassNormLocalHigherUnitExponent_eq_zero_iff
    (v : HeightOneSpectrum (𝓞 K)) :
    ideleClassNormLocalHigherUnitExponent
        (K := K) (L := L) v = 0 ↔
      (v.adicCompletionIntegers K).units ≤
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v := by
  constructor
  · intro hzero
    simpa only [hzero, RayClass.localHigherUnitGroup_zero] using
      ideleClassNormLocalHigherUnitExponent_spec
        (K := K) (L := L) v
  · intro hunits
    apply Nat.eq_zero_of_le_zero
    apply
      ideleClassNormLocalHigherUnitExponent_min
        (K := K) (L := L) v
    simpa only [RayClass.localHigherUnitGroup_zero] using hunits

omit [NumberField L] in
/-- At an unramified chosen completion, the selected local exponent is
zero because the whole local integral-unit group consists of norms. -/
theorem ideleClassNormLocalHigherUnitExponent_eq_zero_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    ideleClassNormLocalHigherUnitExponent
        (K := K) (L := L) v = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.find_min'
    (exists_localHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v)
  rw [RayClass.localHigherUnitGroup_zero]
  exact
    _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v hunram

/-- Outside the finite set of ramified base places, the selected local
higher-unit exponent is zero. -/
theorem ideleClassNormLocalHigherUnitExponent_eq_zero_of_not_mem_ramified
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉ _root_.ramifiedBaseFinitePlaces
        (K := K) (L := L)) :
    ideleClassNormLocalHigherUnitExponent
        (K := K) (L := L) v = 0 := by
  apply
    ideleClassNormLocalHigherUnitExponent_eq_zero_of_chosenUnramified
      (K := K) (L := L) v
  apply
    _root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := L) v
  by_contra hram
  apply hv
  rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
  exact
    ⟨_root_.finitePlaceExtensionCentre
        (K := K) (L := L) v
        (_root_.chosenFinitePlaceExtension (L := L) v),
      _root_.finitePlaceExtensionCentre_liesOver
        (K := K) (L := L) v
        (_root_.chosenFinitePlaceExtension (L := L) v),
      hram⟩

/-- A finite modulus built from the actual local norm subgroups.  Its
support is contained in the finite set of ramified base places. -/
noncomputable def ideleClassNormDefiningModulus :
    RayClass.FiniteModulus K :=
  Finsupp.onFinset
    (_root_.ramifiedBaseFinitePlaces (K := K) (L := L))
    (ideleClassNormLocalHigherUnitExponent (K := K) (L := L))
    (by
      intro v hv
      by_contra hvRamified
      exact
        hv
          (ideleClassNormLocalHigherUnitExponent_eq_zero_of_not_mem_ramified
            (K := K) (L := L) v hvRamified))

/-- Evaluation of the actual norm defining modulus is the selected local
higher-unit exponent. -/
@[simp]
theorem ideleClassNormDefiningModulus_apply
    (v : HeightOneSpectrum (𝓞 K)) :
    ideleClassNormDefiningModulus (K := K) (L := L) v =
      ideleClassNormLocalHigherUnitExponent
        (K := K) (L := L) v :=
  Finsupp.onFinset_apply

/-- The local higher-unit group prescribed by the actual norm defining
modulus lies in the chosen local norm subgroup at every finite place. -/
theorem ideleClassNormDefiningModulus_local_spec
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.localHigherUnitGroup v
        (ideleClassNormDefiningModulus (K := K) (L := L) v) ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  rw [ideleClassNormDefiningModulus_apply]
  exact
    ideleClassNormLocalHigherUnitExponent_spec
      (K := K) (L := L) v

/-- The norm defining modulus is pointwise minimal among all moduli whose
prescribed local higher-unit groups consist of chosen local norms. -/
theorem ideleClassNormDefiningModulus_le_of_localHigherUnitGroup_le
    (m : RayClass.FiniteModulus K)
    (hm :
      ∀ v : HeightOneSpectrum (𝓞 K),
        RayClass.localHigherUnitGroup v (m v) ≤
          _root_.chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := L) v) :
    ideleClassNormDefiningModulus (K := K) (L := L) ≤ m := by
  intro v
  rw [ideleClassNormDefiningModulus_apply]
  exact
    ideleClassNormLocalHigherUnitExponent_min
      (K := K) (L := L) v (hm v)

/-- A finite place occurs in the constructed norm modulus exactly when
some integral unit at that place is not a norm from the chosen localized
extension. -/
theorem mem_ideleClassNormDefiningModulus_support_iff
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈
        (ideleClassNormDefiningModulus
          (K := K) (L := L)).support ↔
      ¬ (v.adicCompletionIntegers K).units ≤
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v := by
  rw [Finsupp.mem_support_iff,
    ideleClassNormDefiningModulus_apply]
  exact
    not_congr
      (ideleClassNormLocalHigherUnitExponent_eq_zero_iff
        (K := K) (L := L) v)



















/-- The raw idele congruence subgroup of the constructed modulus lies
in the image of the actual relative-idele norm. -/
theorem
    ideleCongruenceSubgroup_normDefiningModulus_le_relativeIdeleNorm_range :
    (RayClass.Modulus.narrowOfFinite
        (ideleClassNormDefiningModulus
          (K := K) (L := L))).ideleCongruenceSubgroup ≤
      (RelativeIdeleGroup.norm K L).range := by
  intro a ha
  rw [RayClass.Modulus.ideleCongruenceSubgroup_narrowOfFinite] at ha
  refine
    (_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms
      (K := K) (L := L) a).2 ⟨?_, ?_⟩
  · intro w
    apply
      _root_.infinitePositiveSubgroup_le_infiniteTensorNormSubgroup
        (K := K) (L := L) w
    have hw :=
      (RayClass.mem_narrowInfiniteCongruenceSubgroup_iff a.1).1 ha.1 w
    simpa only [IdeleGroup.infiniteComponent_apply] using hw
  · intro v
    rw [
      _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
    apply
      ideleClassNormDefiningModulus_local_spec
        (K := K) (L := L) v
    have hv :=
      (RayClass.mem_finiteCongruenceSubgroup_iff
        (ideleClassNormDefiningModulus (K := K) (L := L)) a.2).1
          ha.2 v
    simpa only [IdeleGroup.finiteComponent_apply] using hv

/-- The explicitly constructed modulus is a defining modulus for the
actual idele-class norm subgroup. -/
theorem ideleClassNormDefiningModulus_isDefiningModulus :
    IsDefiningModulus
      ((_root_.ideleClassNorm K L).range)
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormDefiningModulus (K := K) (L := L))) := by
  rw [IsDefiningModulus, RayClass.Modulus.congruenceSubgroup,
    Subgroup.map_le_iff_le_comap]
  apply sup_le
  · intro a ha
    change
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a ∈
        (_root_.ideleClassNorm K L).range
    obtain ⟨z, hz⟩ :=
      ideleCongruenceSubgroup_normDefiningModulus_le_relativeIdeleNorm_range
        (K := K) (L := L) ha
    refine
      ⟨QuotientGroup.mk'
          (IdeleGroup.principalSubgroup L)
          (_root_.relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L) z), ?_⟩
    change
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (IdeleGroup.norm K L
            (_root_.relativeIdeleBaseChangeMulEquiv
              (K := K) (L := L) z)) =
        QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a
    rw [IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv, hz]
  · intro a ha
    change
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a ∈
        (_root_.ideleClassNorm K L).range
    have haOne :
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a = 1 :=
      (QuotientGroup.eq_one_iff a).2 ha
    rw [haOne]
    exact ((_root_.ideleClassNorm K L).range).one_mem

/-- The conductorial subgroup supplied by the actual idèle-class norm
range and its explicitly constructed defining modulus. -/
noncomputable def ideleClassNormConductorialSubgroup :
    ConductorialSubgroup K :=
  ⟨(_root_.ideleClassNorm K L).range,
    ⟨RayClass.Modulus.narrowOfFinite
        (ideleClassNormDefiningModulus (K := K) (L := L)),
      ideleClassNormDefiningModulus_isDefiningModulus
        (K := K) (L := L)⟩⟩

/-- The narrow finite conductor of the actual idèle-class norm range. -/

local notation:max "current_ideleClassNormConductorialSubgroup" => ideleClassNormConductorialSubgroup (K := K) (L := L)

noncomputable def ideleClassNormNarrowFiniteConductor :
    RayClass.FiniteModulus K :=
  (current_ideleClassNormConductorialSubgroup).narrowFiniteConductor

/-- The actual idele-class norm subgroup is open in the ordinary
idele-class topology. -/
theorem ideleClassNorm_range_isOpen :
    IsOpen
      (((_root_.ideleClassNorm K L).range :
        Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) := by
  exact
    (current_ideleClassNormConductorialSubgroup).isOpen

/-- The actual idele-class norm subgroup is closed. -/
theorem ideleClassNorm_range_isClosed :
    IsClosed
      (((_root_.ideleClassNorm K L).range :
        Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) :=
  (current_ideleClassNormConductorialSubgroup).isClosed

/-- The actual idele-class norm subgroup has finite index. -/
instance ideleClassNorm_rangeFiniteIndex :
    ((_root_.ideleClassNorm K L).range).FiniteIndex :=
  ConductorialSubgroup.finiteIndex
    (current_ideleClassNormConductorialSubgroup)

/-- The narrow finite conductor itself is a defining modulus for the actual
idele-class norm subgroup. -/

local notation:max "current_ideleClassNormNarrowFiniteConductor" => ideleClassNormNarrowFiniteConductor (K := K) (L := L)

theorem ideleClassNorm_narrowFiniteConductor_isDefiningModulus :
    IsDefiningModulus
      ((_root_.ideleClassNorm K L).range)
      (RayClass.Modulus.narrowOfFinite
        (current_ideleClassNormNarrowFiniteConductor)) :=
  (current_ideleClassNormConductorialSubgroup).narrowFiniteConductor_isDefiningModulus

/-- The canonical quotient map from the ray class group at the actual
narrow finite norm conductor onto the actual idèle-class norm quotient. -/
noncomputable def
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient :
    RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite
          (current_ideleClassNormNarrowFiniteConductor)) →*
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range :=
  QuotientGroup.map
    (RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite
        (current_ideleClassNormNarrowFiniteConductor)))
    ((_root_.ideleClassNorm K L).range)
    (MonoidHom.id _)
    (fun _ hx =>
      ideleClassNorm_narrowFiniteConductor_isDefiningModulus
        (K := K) (L := L) hx)

/-- The narrow finite conductor ray-class quotient map sends an idèle class to its
class modulo the actual norm subgroup. -/
@[simp]
theorem narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk
    (x : IdeleClassGroup K) :
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
        (K := K) (L := L)
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite
              (current_ideleClassNormNarrowFiniteConductor))) x) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K L).range) x :=
  rfl

























































































































































/-- The narrow finite conductor of the actual norm subgroup is bounded by
the modulus obtained from the chosen local norm subgroups. -/
theorem ideleClassNorm_narrowFiniteConductor_le_normDefiningModulus :
    current_ideleClassNormNarrowFiniteConductor ≤
      ideleClassNormDefiningModulus (K := K) (L := L) :=
  (current_ideleClassNormConductorialSubgroup).narrowFiniteConductor_le
    (ideleClassNormDefiningModulus_isDefiningModulus
      (K := K) (L := L))







































/-- If the zeroth one-place higher-unit class subgroup lies in the
actual idèle-class norm range, then that finite place is absent from
the narrow finite conductor support. -/
theorem
    not_mem_ideleClassNorm_narrowFiniteConductor_support_of_localHigherUnitClassSubgroup_zero_le
    (v : HeightOneSpectrum (𝓞 K))
    (hlocal :
      RayClass.localHigherUnitClassSubgroup v 0 ≤
        (_root_.ideleClassNorm K L).range) :
    v ∉
      (current_ideleClassNormNarrowFiniteConductor).support := by
  change v ∉
    (current_ideleClassNormConductorialSubgroup).narrowFiniteConductor.support
  rw [Finsupp.notMem_support_iff,
    (current_ideleClassNormConductorialSubgroup).narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent v]
  exact
    Nat.eq_zero_of_le_zero
      ((current_ideleClassNormConductorialSubgroup).narrowFiniteLocalConductorExponent_le v hlocal)

/-- If the chosen prime of `L` above `v` is algebraically unramified,
then `v` does not occur in the conductor of the actual idele-class norm
subgroup. -/
theorem
    not_mem_ideleClassNorm_narrowFiniteConductor_support_of_isUnramifiedAt
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v)).asIdeal) :
    v ∉
      (current_ideleClassNormNarrowFiniteConductor).support := by
  apply
    not_mem_ideleClassNorm_narrowFiniteConductor_support_of_localHigherUnitClassSubgroup_zero_le
      (K := K) (L := L) v
  exact
    localHigherUnitClassSubgroup_zero_le_ideleClassNorm_range_of_isUnramifiedAt
      (K := K) (L := L) v hunram






















/-- The narrow finite conductor of an actual finite Galois idèle-class norm
subgroup is supported only at ramified finite places of the base field. -/
theorem ideleClassNorm_narrowFiniteConductor_support_subset_ramifiedBaseFinitePlaces :
    (current_ideleClassNormNarrowFiniteConductor).support ⊆
      _root_.ramifiedBaseFinitePlaces
        (K := K) (L := L) := by
  intro v hv
  by_contra hvRamified
  have hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v)).asIdeal := by
    by_contra hram
    apply hvRamified
    rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
    exact
      ⟨_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v),
        _root_.finitePlaceExtensionCentre_liesOver
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v),
        hram⟩
  exact
    (not_mem_ideleClassNorm_narrowFiniteConductor_support_of_isUnramifiedAt
      (K := K) (L := L) v hunram) hv

end GlobalClassFields
end GlobalClassFieldTheory

end
