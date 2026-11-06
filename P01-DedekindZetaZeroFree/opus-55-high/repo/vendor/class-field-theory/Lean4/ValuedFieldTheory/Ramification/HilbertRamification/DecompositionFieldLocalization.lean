module

public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
public import ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
public import ValuedFieldTheory.Ramification.HilbertRamification.LocalizationDensity
public import ValuedFieldTheory.Ramification.HilbertRamification.DecompositionField
public import ValuedFieldTheory.Valuation.Completion.ExtensionInvariants
public import Mathlib.FieldTheory.SeparableClosure

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Decomposition-field value and residue comparison

This file identifies the decomposition field with the literal intersection
`L ∩ K_v` inside the algebraic localization `L_w`.  It then records the
canonical residue-field isomorphism and equality of absolute-value ranges in
the nonarchimedean case.
-/

noncomputable section

universe u v

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

section LocalizationGalois

variable [IsGalois K L]
variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
  (w : AbsoluteValueExtension vK L)

local instance proposition98CompletionBaseAlgebra : Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := K) w.1

local instance proposition98CompletionBaseSMul : SMul K w.1.Completion :=
  (AbsoluteValue.extensionCompletionAlgebra (K := K) w.1).toSMul

local instance proposition98CompletionAlgebra : Algebra vK.Completion w.1.Completion :=
  AbsoluteValue.completionAlgebra vK w.1 w.2

 abbrev decompositionFieldAlgebraicLocalization : IntermediateField vK.Completion w.1.Completion :=
  AbsoluteValue.algebraicLocalization vK w.1 w.2

 abbrev decompositionFieldAlgebraicLocalizationEmbedding : L →+* decompositionFieldAlgebraicLocalization vK w :=
  AbsoluteValue.toAlgebraicLocalization vK w.1 w.2

local instance proposition98LocalizationBaseAlgebra : Algebra K (decompositionFieldAlgebraicLocalization vK w) :=
  ((algebraMap vK.Completion (decompositionFieldAlgebraicLocalization vK w)).comp
    (algebraMap K vK.Completion)).toAlgebra

local instance proposition98LocalizationScalarTower :
    IsScalarTower K vK.Completion (decompositionFieldAlgebraicLocalization vK w) :=
  IsScalarTower.of_algebraMap_eq' (by
    rfl)

/-- The dense copy of `L` in the localization, as a `K`-algebra embedding
for the scalar tower `K → K_v → L_w`. -/
def decompositionField_toLocalizationAlgHom :
    L →ₐ[K] decompositionFieldAlgebraicLocalization vK w where
  __ := decompositionFieldAlgebraicLocalizationEmbedding vK w
  commutes' x := AbsoluteValue.toAlgebraicLocalization_algebraMap vK w.1 w.2 x

omit [IsGalois K L] in
/-- The localization is generated over `K_v` by the subtype-valued copy of
`L`, not only by its ambient-completion representatives. -/
theorem decompositionField_localization_adjoin_range_eq_top :
    IntermediateField.adjoin vK.Completion
      (Set.range (decompositionFieldAlgebraicLocalizationEmbedding vK w)) = ⊤ := by
  let E := decompositionFieldAlgebraicLocalization vK w
  apply IntermediateField.lift_injective E
  rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
  change IntermediateField.adjoin vK.Completion
      (Subtype.val '' Set.range (decompositionFieldAlgebraicLocalizationEmbedding vK w)) =
    AbsoluteValue.algebraicLocalization vK w.1 w.2
  congr 1
  ext z
  simp

omit hvK in
/-- Every generator coming from `L` is separable over `K_v`. -/
theorem decompositionField_toLocalization_isSeparable (x : L) :
    IsSeparable vK.Completion (decompositionFieldAlgebraicLocalizationEmbedding vK w x) := by
  have hx : IsSeparable K
      (decompositionField_toLocalizationAlgHom vK w x) :=
    (Algebra.IsSeparable.isSeparable K x).map
      (decompositionField_toLocalizationAlgHom vK w)
      (decompositionField_toLocalizationAlgHom vK w).injective
  exact IsSeparable.tower_top vK.Completion hx

omit hvK in
/-- Every generator coming from `L` has its `K_v`-minimal polynomial split
inside the localization. -/
theorem decompositionField_toLocalization_minpoly_splits (x : L) :
    ((minpoly vK.Completion (decompositionFieldAlgebraicLocalizationEmbedding vK w x)).map
      (algebraMap vK.Completion (decompositionFieldAlgebraicLocalization vK w))).Splits := by
  let i := decompositionField_toLocalizationAlgHom vK w
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hsK : ((minpoly K x).map
      (algebraMap K (decompositionFieldAlgebraicLocalization vK w))).Splits := by
    have hi : i.toRingHom.comp (algebraMap K L) =
        algebraMap K (decompositionFieldAlgebraicLocalization vK w) := i.comp_algebraMap
    have hs := (Normal.splits (F := K) (K := L) inferInstance x).map
      i.toRingHom
    simpa only [Polynomial.map_map, hi] using hs
  have hsTower : (((minpoly K x).map (algebraMap K vK.Completion)).map
      (algebraMap vK.Completion (decompositionFieldAlgebraicLocalization vK w))).Splits := by
    simpa only [Polynomial.map_map,
      IsScalarTower.algebraMap_eq K vK.Completion (decompositionFieldAlgebraicLocalization vK w)] using hsK
  have hdvd : minpoly vK.Completion (decompositionFieldAlgebraicLocalizationEmbedding vK w x) ∣
      (minpoly K x).map (algebraMap K vK.Completion) := by
    have h := minpoly.dvd_map_of_isScalarTower K vK.Completion
      (decompositionFieldAlgebraicLocalizationEmbedding vK w x)
    have hmin : minpoly K (decompositionFieldAlgebraicLocalizationEmbedding vK w x) = minpoly K x :=
      minpoly.algHom_eq i i.injective x
    rwa [hmin] at h
  exact hsTower.of_dvd
    (Polynomial.map_ne_zero
      (Polynomial.map_ne_zero (minpoly.ne_zero hxint)))
    ((Polynomial.map_dvd_map' _).mpr hdvd)

omit hvK in
/-- The algebraic localization of a Galois extension is normal over the
completed base field, with no finite-degree hypothesis. -/
theorem decompositionField_localization_normal :
    Normal vK.Completion (decompositionFieldAlgebraicLocalization vK w) := by
  let : Algebra.IsAlgebraic vK.Completion (decompositionFieldAlgebraicLocalization vK w) :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  rw [normal_iff]
  intro z
  refine ⟨Algebra.IsIntegral.isIntegral z, ?_⟩
  apply IntermediateField.splits_of_mem_adjoin
      (F := vK.Completion) (K := decompositionFieldAlgebraicLocalization vK w)
      (L := decompositionFieldAlgebraicLocalization vK w)
      (S := Set.range (decompositionFieldAlgebraicLocalizationEmbedding vK w))
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ⟨(decompositionField_toLocalization_isSeparable vK w x).isIntegral,
      decompositionField_toLocalization_minpoly_splits vK w x⟩
  · rw [decompositionField_localization_adjoin_range_eq_top vK w]
    trivial

omit hvK in
/-- The algebraic localization of a Galois extension is separable over the
completed base field, with no finite-degree hypothesis. -/
theorem decompositionField_localization_separable :
    Algebra.IsSeparable vK.Completion (decompositionFieldAlgebraicLocalization vK w) := by
  let S := Set.range (decompositionFieldAlgebraicLocalizationEmbedding vK w)
  have hS : Algebra.IsSeparable vK.Completion
      (IntermediateField.adjoin vK.Completion S) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable
      (F := vK.Completion) (E := decompositionFieldAlgebraicLocalization vK w)).mpr fun y hy => by
      rcases hy with ⟨x, rfl⟩
      exact decompositionField_toLocalization_isSeparable vK w x
  let : Algebra.IsSeparable vK.Completion
      (IntermediateField.adjoin vK.Completion S) := hS
  refine ⟨fun z => ?_⟩
  have hz : z ∈ IntermediateField.adjoin vK.Completion S := by
    rw [decompositionField_localization_adjoin_range_eq_top vK w]
    trivial
  exact IntermediateField.isSeparable_of_mem_isSeparable vK.Completion
    (decompositionFieldAlgebraicLocalization vK w) hz

omit hvK in
/-- The algebraic localization of a Galois extension is Galois over `K_v`.
This permits the fixed-field argument in infinite degree. -/
theorem algebraicLocalization_isGalois :
    IsGalois vK.Completion (decompositionFieldAlgebraicLocalization vK w) :=
  isGalois_iff.mpr
    ⟨decompositionField_localization_separable vK w,
      decompositionField_localization_normal vK w⟩

include hvK

omit hvK

include hvK

omit hvK

include hvK

omit hvK
