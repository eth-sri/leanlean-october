module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Ramification ideals in finite complete-DVF extensions

This file records the ideal-theoretic source behind the local-field structure theory.
The base maximal ideal maps to the `e`-th power of the target maximal ideal, where
`e` is the canonical ramification index.  Every statement is expressed directly
in the ambient valued-extension context; no extension marker is involved.
-/


universe u v w x

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace ValuedExtension
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- No power of the target maximal ideal is contained in the next power.

This is the ideal-level form of the uniformizer-power separation lemma. -/
theorem target_maximalIdeal_pow_not_le_pow_succ
    {π : target.valuationSubring}
    (hπ : target.valuation.IsUniformizer (π : L)) (n : ℕ) :
    ¬ target.maximalIdeal ^ n ≤ target.maximalIdeal ^ (n + 1) := by
  intro hle
  have hπpow_mem : π ^ n ∈ target.maximalIdeal ^ n := by
    rw [target.maximalIdeal_pow_eq_span_uniformizer_pow hπ n]
    simp
  exact target.uniformizer_pow_not_mem_maximalIdeal_pow_succ hπ n
    (hle hπpow_mem)

/-- The image of the base maximal ideal is the `e`-th power of the target
maximal ideal. -/
theorem maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex :
    Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal =
      target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF := by
  rcases target.nonzero_ideal_eq_maximalIdeal_pow
      (Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal)
      (maximalIdeal_map_integerMap_ne_bot base.toDVF target.toDVF) with
    ⟨n, hn⟩
  have hle :
      Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal ≤
        target.maximalIdeal ^ n := by
    rw [hn]
  have hnot :
      ¬ Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal ≤
        target.maximalIdeal ^ (n + 1) := by
    intro hle_succ
    rcases target.exists_uniformizer with ⟨π, hπ⟩
    exact target_maximalIdeal_pow_not_le_pow_succ target hπ n
      (by simpa [hn] using hle_succ)
  have he : ramificationIndex base.toDVF target.toDVF = n := by
    simpa [ramificationIndex, integerMap] using
      (Ideal.ramificationIdx'_spec
        (p := base.maximalIdeal) (P := target.maximalIdeal) hle hnot)
  rw [he]
  exact hn

/-- The image of a base uniformizer generates the `e`-th target maximal-ideal
power. -/
theorem span_base_uniformizer_image_eq_target_maximalIdeal_pow_ramificationIndex
    {ϖ : base.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K)) :
    Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
        Set target.valuationSubring) =
      target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF := by
  calc
    Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
        Set target.valuationSubring) =
        Ideal.map (integerMap base.toDVF target.toDVF)
          (Ideal.span ({ϖ} : Set base.valuationSubring)) := by
      rw [Ideal.map_span, Set.image_singleton]
    _ = Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal := by
      rw [base.maximalIdeal_eq_span_uniformizer hϖ]
    _ = target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF :=
      maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex base target

/-- The image of a base uniformizer lies in the `e`-th target maximal-ideal
power. -/
theorem base_uniformizer_image_mem_target_maximalIdeal_pow_ramificationIndex
    {ϖ : base.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K)) :
    integerMap base.toDVF target.toDVF ϖ ∈
      target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF := by
  rw [← span_base_uniformizer_image_eq_target_maximalIdeal_pow_ramificationIndex
    base target hϖ]
  simp

/-- The image of a base uniformizer is a unit multiple of the `e`-th power of
any target uniformizer. -/
theorem exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image
    {ϖ : base.valuationSubring} {π : target.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K))
    (hπ : target.valuation.IsUniformizer (π : L)) :
    ∃ u : target.valuationSubringˣ,
      integerMap base.toDVF target.toDVF ϖ =
        (u : target.valuationSubring) *
          π ^ ramificationIndex base.toDVF target.toDVF := by
  have hspan :
      Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
          Set target.valuationSubring) =
        target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF :=
    span_base_uniformizer_image_eq_target_maximalIdeal_pow_ramificationIndex
      base target hϖ
  have hx_mem :
      integerMap base.toDVF target.toDVF ϖ ∈
        target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF :=
    base_uniformizer_image_mem_target_maximalIdeal_pow_ramificationIndex
      base target hϖ
  rcases
      (target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd hπ
        (ramificationIndex base.toDVF target.toDVF)).1 hx_mem with
    ⟨u, hu⟩
  have hu_unit : IsUnit u := by
    by_contra hnot_unit
    have hu_mem : u ∈ target.maximalIdeal := by
      simp_all
    have hπpow_mem :
        π ^ ramificationIndex base.toDVF target.toDVF ∈
          target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF := by
      rw [target.maximalIdeal_pow_eq_span_uniformizer_pow hπ
        (ramificationIndex base.toDVF target.toDVF)]
      simp
    have hx_deep :
        integerMap base.toDVF target.toDVF ϖ ∈
          target.maximalIdeal ^
            (ramificationIndex base.toDVF target.toDVF + 1) := by
      rw [hu]
      have hmul :
          π ^ ramificationIndex base.toDVF target.toDVF * u ∈
            target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF *
              target.maximalIdeal :=
        Ideal.mul_mem_mul hπpow_mem hu_mem
      simpa [pow_succ] using hmul
    have hspan_le :
        Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
            Set target.valuationSubring) ≤
          target.maximalIdeal ^
            (ramificationIndex base.toDVF target.toDVF + 1) := by
      rw [Ideal.span_le]
      simp_all
    exact target_maximalIdeal_pow_not_le_pow_succ target hπ
      (ramificationIndex base.toDVF target.toDVF)
      (by simpa [hspan] using hspan_le)
  rcases hu_unit with ⟨uunit, huunit⟩
  refine ⟨uunit, ?_⟩
  simpa [huunit, mul_comm] using hu
