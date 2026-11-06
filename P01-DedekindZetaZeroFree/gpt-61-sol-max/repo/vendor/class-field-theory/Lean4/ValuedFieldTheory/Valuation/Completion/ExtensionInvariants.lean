module

public import ValuedFieldTheory.Valuation.AbsoluteValue.Completion
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaIntegralClosure
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueExtensionCoefficients
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
public import ValuedFieldTheory.Valuation.AbsoluteValue.Completeness
public import ValuedFieldTheory.Valuation.AbsoluteValue.ExponentialValuation
public import ValuedFieldTheory.Valuation.AbsoluteValue.Extension
public import ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean
public import ValuedFieldTheory.Valuation.AbsoluteValue.Ostrowski
public import ValuedFieldTheory.Valuation.AbsoluteValue.PrincipalAdicCompleteness
public import ValuedFieldTheory.Valuation.AbsoluteValue.SpectralExtension
public import ValuedFieldTheory.Valuation.AbsoluteValue.Theory.Core
public import ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
public import ValuedFieldTheory.Valuation.Completion.DegreeNormTrace
public import ValuedFieldTheory.Valuation.Henselian.Complete

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

























set_option autoImplicit false

/-!
# Local degree, ramification, and residue invariants

For a finite separable extension `L / K` and a discrete nonarchimedean
absolute value `v` on `K`, this file proves the exact degree formula
`∑_{w ∣ v} e_w f_w = [L : K]`.

The proof makes explicit the two facts used implicitly in the construction: metric
completion preserves the value group and residue field, and every completed
local extension `L_w / K_v` is finite separable.  The fundamental inequality then gives
`[L_w : K_v] = e_w f_w`; summing and applying the local degree, norm, and trace formulas gives the result.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicNumberTheory.Valuations

universe u v

 theorem completionNonarchimedean
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (AbsoluteValue.completionAbsoluteValue vK) :=
  (AbsoluteValue.isNonarchimedean_iff_bounded_nat
    (AbsoluteValue.completionAbsoluteValue vK)).1
    (AbsoluteValue.completionAbsoluteValue_isNonarchimedean vK
      ((AbsoluteValue.isNonarchimedean_iff_bounded_nat vK).2 hv))

theorem mem_absoluteValueExponentialSubring_iff
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) (x : K) :
    x ∈ LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation a ha) ↔ a x ≤ 1 := by
  rw [LubinTate.Valuations.mem_exponentialValuationSubring_iff]
  by_cases hx : x = 0
  · subst x
    simp [absoluteValueExponentialValuation]
  · rw [absoluteValueExponentialValuation_apply_ne_zero a ha hx]
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.coe_nonneg]
    constructor
    · intro h
      by_contra hnot
      have hone : 1 < a x := lt_of_not_ge hnot
      linarith [Real.log_pos hone]
    · intro h
      exact neg_nonneg.mpr (Real.log_nonpos (a.nonneg x) h)





























































theorem mem_absoluteValueExponentialSubring_maximalIdeal_iff
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (x : LubinTate.Valuations.exponentialValuationSubring
      (absoluteValueExponentialValuation a ha)) :
    x ∈ IsLocalRing.maximalIdeal
        (LubinTate.Valuations.exponentialValuationSubring
          (absoluteValueExponentialValuation a ha)) ↔
      a (x : K) < 1 := by
  rw [← LubinTate.Valuations.exponentialMaxIdeal_eq_maximalIdeal]
  change (0 : WithTop ℝ) <
      absoluteValueExponentialValuation a ha (x : K) ↔ _
  by_cases hx : (x : K) = 0
  · simp [hx, absoluteValueExponentialValuation]
  · exact (LubinTate.Valuations.associatedAbsoluteValue_lt_one_iff
      (absoluteValueExponentialValuation_associated a ha) hx).symm

/-- The homomorphism from the exponential valuation subring of a field to that
of its completion, induced by the canonical map into the completion. -/
def completionExponentialSubringMap
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) :
    LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation a ha) →+*
      LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation
          (AbsoluteValue.completionAbsoluteValue a)
          (completionNonarchimedean a ha)) :=
  (algebraMap K a.Completion).restrict _ _ fun x hx => by
    rw [mem_absoluteValueExponentialSubring_iff] at hx ⊢
    change AbsoluteValue.completionAbsoluteValue a (x : a.Completion) ≤ 1
    rw [AbsoluteValue.completionAbsoluteValue_coe]
    exact hx

@[simp] theorem completionExponentialSubringMap_apply
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (x : LubinTate.Valuations.exponentialValuationSubring
      (absoluteValueExponentialValuation a ha)) :
    ((completionExponentialSubringMap a ha x :
      LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation
          (AbsoluteValue.completionAbsoluteValue a)
          (completionNonarchimedean a ha))) : a.Completion) =
      algebraMap K a.Completion (x : K) := rfl

theorem completionExponentialSubringMap_isLocalHom
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) :
    IsLocalHom (completionExponentialSubringMap a ha) := by
  constructor
  intro x hx
  rw [LubinTate.Valuations.associatedAbsoluteValue_isUnit_iff_eq_one
    (absoluteValueExponentialValuation_associated a ha)]
  rw [LubinTate.Valuations.associatedAbsoluteValue_isUnit_iff_eq_one
    (absoluteValueExponentialValuation_associated
      (AbsoluteValue.completionAbsoluteValue a)
      (completionNonarchimedean a ha))] at hx
  change AbsoluteValue.completionAbsoluteValue a
      ((x : K) : a.Completion) = 1 at hx
  rw [AbsoluteValue.completionAbsoluteValue_coe] at hx
  exact hx

theorem completionResidueMap_surjective
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) :
    letI : IsLocalHom (completionExponentialSubringMap a ha) :=
      completionExponentialSubringMap_isLocalHom a ha
    Function.Surjective
      (IsLocalRing.ResidueField.map (completionExponentialSubringMap a ha)) := by
  let v := absoluteValueExponentialValuation a ha
  let aC := AbsoluteValue.completionAbsoluteValue a
  let haC := completionNonarchimedean a ha
  let vC := absoluteValueExponentialValuation aC haC
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let VC := LubinTate.Valuations.exponentialValuationSubring vC
  let f : V →+* VC := completionExponentialSubringMap a ha
  let : IsLocalHom f := completionExponentialSubringMap_isLocalHom a ha
  intro z
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  let vId : AbsoluteValueExtension a K := ⟨a, fun _ => rfl⟩
  obtain ⟨x, hx⟩ :=
    (AbsoluteValue.denseRange_toCompletion vId.1).exists_dist_lt
      (y : a.Completion) zero_lt_one
  have hclose : aC (algebraMap K a.Completion x - (y : a.Completion)) < 1 := by
    change ‖algebraMap K a.Completion x - (y : a.Completion)‖ < 1
    rw [dist_eq_norm] at hx
    change ‖(y : a.Completion) - algebraMap K a.Completion x‖ < 1 at hx
    simpa only [norm_sub_rev] using hx
  have hy_le : aC (y : a.Completion) ≤ 1 := by
    exact (mem_absoluteValueExponentialSubring_iff aC haC (y : a.Completion)).1 y.property
  have hx_leC : aC (algebraMap K a.Completion x) ≤ 1 := by
    calc
      aC (algebraMap K a.Completion x) =
          aC ((algebraMap K a.Completion x - (y : a.Completion)) + y) := by
            congr 1
            ring
      _ ≤ max (aC (algebraMap K a.Completion x - (y : a.Completion)))
          (aC (y : a.Completion)) :=
        LubinTate.Valuations.strong_triangle_of_nonarchimedean aC haC _ _
      _ ≤ 1 := max_le hclose.le hy_le
  have hx_le : a x ≤ 1 := by
    change aC (x : a.Completion) ≤ 1 at hx_leC
    rwa [AbsoluteValue.completionAbsoluteValue_coe] at hx_leC
  let xV : V := ⟨x, (mem_absoluteValueExponentialSubring_iff a ha x).2 hx_le⟩
  refine ⟨IsLocalRing.residue V xV, ?_⟩
  rw [IsLocalRing.ResidueField.map_residue]
  rw [ValuationTheory.DiscreteValuationField.ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal]
  rw [mem_absoluteValueExponentialSubring_maximalIdeal_iff aC haC]
  exact hclose

/-- The residue-field equivalence induced by the canonical map from a
nonarchimedean valued field to its completion. -/
noncomputable def completionResidueEquiv
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) :
    IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubring
          (absoluteValueExponentialValuation a ha)) ≃+*
      IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubring
          (absoluteValueExponentialValuation
            (AbsoluteValue.completionAbsoluteValue a)
            (completionNonarchimedean a ha))) := by
  letI : IsLocalHom (completionExponentialSubringMap a ha) :=
    completionExponentialSubringMap_isLocalHom a ha
  exact ValuationTheory.DiscreteValuationField.ResidueField.ringEquivOfSurjective
    (completionExponentialSubringMap a ha)
    (completionResidueMap_surjective a ha)

@[simp] theorem completionResidueEquiv_residue
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (x : LubinTate.Valuations.exponentialValuationSubring
      (absoluteValueExponentialValuation a ha)) :
    completionResidueEquiv a ha
        (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (completionExponentialSubringMap a ha x) := by
  let : IsLocalHom (completionExponentialSubringMap a ha) :=
    completionExponentialSubringMap_isLocalHom a ha
  exact IsLocalRing.ResidueField.map_residue _ _









































































































































































































































































































end AlgebraicNumberTheory.Valuations

end
