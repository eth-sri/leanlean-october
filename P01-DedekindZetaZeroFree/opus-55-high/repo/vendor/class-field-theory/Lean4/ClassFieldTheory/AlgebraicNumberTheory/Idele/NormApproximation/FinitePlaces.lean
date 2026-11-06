module

public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Approximation
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.HerbrandEquiv
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Finite
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.H0
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.HMinusOne
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
public import ValuedFieldTheory.Valuation.Completion.ExtensionFactorClassification

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Weak approximation for actual local norm quotients

For a finite Galois extension `L / K` and a finite set `S` of finite
places of `K`, this file chooses an actual extension of every `v ∈ S`,
forms the corresponding algebraic localization `L_w / K_v`, and
transports its local norm subgroup to mathlib's concrete adic
completion.  These transported norm subgroups are open.  Multiplicative
weak approximation therefore gives a surjection

`Kˣ → ∏ v ∈ S, K_vˣ / N(L_wˣ)`.

All choices are made from the extension theorem for absolute values;
none of the local conclusions is included as input data.
-/

open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The canonical dense embedding used to compare the absolute-value
completion at `v` with the concrete adic completion. -/
def finitePlaceCompletionBaseMap
    (v : HeightOneSpectrum (𝓞 K)) :
    WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) →+*
      v.adicCompletion K :=
  (FinitePlace.embedding v).comp
    (WithAbs.equiv
      (NumberField.HeightOneSpectrum.adicAbv K v)).toRingHom

@[simp]
theorem finitePlaceCompletionBaseMap_apply
    (v : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K v)) :
    finitePlaceCompletionBaseMap v x =
      FinitePlace.embedding v
        (WithAbs.equiv
          (NumberField.HeightOneSpectrum.adicAbv K v) x) :=
  rfl

theorem finitePlaceCompletionBaseMap_norm
    (v : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K v)) :
    ‖finitePlaceCompletionBaseMap v x‖ = ‖x‖ := by
  rw [finitePlaceCompletionBaseMap_apply,
    FinitePlace.norm_embedding]
  rfl

/-- The base embedding is an isometry. -/
theorem finitePlaceCompletionBaseMap_isometry
    (v : HeightOneSpectrum (𝓞 K)) :
    Isometry (finitePlaceCompletionBaseMap v) :=
  AddMonoidHomClass.isometry_of_norm _
    (finitePlaceCompletionBaseMap_norm v)

/-- Extension of the base embedding to the absolute-value completion. -/
def finitePlaceCompletionRingHom
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion →+*
      v.adicCompletion K :=
  UniformSpace.Completion.extensionHom
    (finitePlaceCompletionBaseMap v)
    (finitePlaceCompletionBaseMap_isometry v).continuous

@[simp]
theorem finitePlaceCompletionRingHom_coe
    (v : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K v)) :
    finitePlaceCompletionRingHom v
        (x :
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion) =
      finitePlaceCompletionBaseMap v x :=
  UniformSpace.Completion.extensionHom_coe
    (finitePlaceCompletionBaseMap v)
    (finitePlaceCompletionBaseMap_isometry v).continuous x

theorem finitePlaceCompletionRingHom_isometry
    (v : HeightOneSpectrum (𝓞 K)) :
    Isometry (finitePlaceCompletionRingHom v) :=
  (finitePlaceCompletionBaseMap_isometry v).completion_extension

/-- The completed comparison map is onto the concrete adic
completion. -/
theorem finitePlaceCompletionRingHom_surjective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (finitePlaceCompletionRingHom v) := by
  let f := finitePlaceCompletionRingHom v
  have hrangeClosed : IsClosed (Set.range f) :=
    (finitePlaceCompletionRingHom_isometry v).isClosedEmbedding.isClosed_range
  have hdense :
      DenseRange (algebraMap K (v.adicCompletion K)) :=
    v.denseRange_algebraMap K
  have hrange :
      Set.range (algebraMap K (v.adicCompletion K)) ⊆
        Set.range f := by
    rintro _ ⟨x, rfl⟩
    let x' : WithAbs
        (NumberField.HeightOneSpectrum.adicAbv K v) :=
      (WithAbs.equiv
        (NumberField.HeightOneSpectrum.adicAbv K v)).symm x
    refine
      ⟨(x' :
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion),
        ?_⟩
    rw [finitePlaceCompletionRingHom_coe]
    rfl
  intro x
  have hx :
      x ∈ closure
        (Set.range (algebraMap K (v.adicCompletion K))) := by
    rw [hdense.closure_range]
    trivial
  exact closure_minimal hrange hrangeClosed hx

/-- The two concrete models of `K_v` are canonically isomorphic. -/
def finitePlaceCompletionRingEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion ≃+*
      v.adicCompletion K :=
  RingEquiv.ofBijective (finitePlaceCompletionRingHom v)
    ⟨(finitePlaceCompletionRingHom_isometry v).injective,
      finitePlaceCompletionRingHom_surjective v⟩

/-- The preceding ring equivalence, with its native topologies. -/
def finitePlaceCompletionContinuousMulEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion ≃ₜ*
      v.adicCompletion K where
  __ := (finitePlaceCompletionRingEquiv v).toMulEquiv
  continuous_toFun :=
    (finitePlaceCompletionRingHom_isometry v).continuous
  continuous_invFun :=
    ((finitePlaceCompletionRingHom_isometry v).right_inv
      (finitePlaceCompletionRingEquiv v).right_inv).continuous

/-- The induced topological multiplicative equivalence on unit
groups. -/
def finitePlaceCompletionUnitsContinuousMulEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completionˣ ≃ₜ*
      (v.adicCompletion K)ˣ :=
  Units.mapContinuousMulEquiv
    (finitePlaceCompletionContinuousMulEquiv v)

/-- The chosen extension of the `v`-adic absolute value to `L`.
The embedding is supplied by algebraic closedness of the completion's
algebraic closure. -/
def chosenFinitePlaceExtension
    (v : HeightOneSpectrum (𝓞 K)) :
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L :=
  pullbackAbsoluteValueExtension
    (NumberField.HeightOneSpectrum.adicAbv K v)
    (RayClass.adicAbv_isNontrivial v)
    IsAlgClosed.lift

/-- The chosen actual localization `L_w` above the finite place `v`. -/
abbrev ChosenFinitePlaceLocalizedCompletion
    (v : HeightOneSpectrum (𝓞 K)) :=
  LocalizedCompletion
    (NumberField.HeightOneSpectrum.adicAbv K v)
    (chosenFinitePlaceExtension (L := L) v)

/-- The concrete local norm subgroup at `v`.  It is first formed in the
absolute-value completion model and then transported to the adic
completion used by the idele library. -/
def chosenFinitePlaceLocalNormSubgroup
    (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (v.adicCompletion K)ˣ := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := LocalizedCompletion vK w
  let e :
      vK.Completionˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  exact
    (localNormSubgroup vK.Completion E).map
      e.toMonoidHom

/-- The local norm subgroup transported to the actual finite idele
coordinate is open. -/
theorem chosenFinitePlaceLocalNormSubgroup_isOpen
    (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen
      (chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v :
        Set (v.adicCompletion K)ˣ) := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let E := LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion E :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField
      vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let : IsUltrametricDist vK.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        vK
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
          K v))
  let : Valued vK.Completion ℝ≥0 :=
    NormedField.toValued
  let vC : Valuation vK.Completion ℝ≥0 := Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vK.Completion)).IsNontrivial)
  let : ValuativeRel vK.Completion :=
    ValuativeRel.ofValuation vC
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  let : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  let : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let e :
      vK.Completionˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  have hN :
      IsOpen
        (localNormSubgroup vK.Completion E :
          Set vK.Completionˣ) :=
    LocalClassFieldTheory.localNormSubgroup_isOpen
      vK.Completion E
  change IsOpen
    (e '' (localNormSubgroup vK.Completion E :
      Set vK.Completionˣ))
  exact e.isOpenMap _ hN
