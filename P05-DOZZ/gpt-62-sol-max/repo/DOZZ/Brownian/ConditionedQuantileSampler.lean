/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedQuantileMeasurable
public import DOZZ.Brownian.ConditionedKernelGridComparison
public import DOZZ.Brownian.ConditionedEntranceProbability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The generalized quantile samples its probability law

The common-uniform coupling uses generalized CDF inverses. This file verifies that the inverse
map, under a uniform level, has exactly the input probability law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Topology
open scoped Topology

namespace DOZZ.Proofs

/-- On uniform levels, the generalized inverse lies below `x` exactly when the CDF at `x`
reaches the level. -/
theorem cdfGeneralizedQuantile_le_iff
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {u x : ℝ}
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u ≤ x ↔
      u ≤ ProbabilityTheory.cdf μ x := by
  let F := ProbabilityTheory.cdf μ
  let S  := {y | u ≤ F y}
  have hnonempty : S.Nonempty := by
    exact Exists.casesOn (eventually_atTop.mp (Tendsto.eventually (tendsto_cdf_atTop μ) (Ioi_mem_nhds hu1))) fun y hy =>
      Exists.intro y (le_of_lt (hy y le_rfl))
  have hbounded : BddBelow S := by
    have hev  :=
      (ProbabilityTheory.tendsto_cdf_atBot μ).eventually (Iio_mem_nhds hu)
    obtain ⟨a, ha⟩ := Filter.eventually_atBot.1 hev
    refine ⟨a, ?_⟩
    intro y hy
    grind
  change sInf S ≤ x ↔ u ≤ F x
  constructor
  · intro hqx
    have hseq0 : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop (𝓝 x) := by
      have hsmall : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.add hsmall
    have hseq : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop
        (𝓝[Set.Ici x] x) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hseq0, Filter.Eventually.of_forall ?_⟩
      intro n
      simp only [Set.mem_Ici]
      exact le_add_of_nonneg_right (by positivity)
    have hFright  :=
      F.right_continuous x |>.tendsto
    have hFseq : Tendsto (fun n : ℕ => F (x + 1 / ((n : ℝ) + 1))) atTop
        (𝓝 (F x)) := by
      convert hFright.comp hseq using 1
      rfl
    have hvalues : ∀ n : ℕ, u ≤ F (x + 1 / ((n : ℝ) + 1)) := by
      intro n
      by_contra hnot
      have hlt  := lt_of_not_ge hnot
      have hbelow : x + 1 / ((n : ℝ) + 1) ≤ sInf S := by
        apply le_csInf hnonempty
        intro y hy
        change u ≤ F y at hy
        by_contra hxy
        have hyx  := le_of_lt (lt_of_not_ge hxy)
        have hmono := ProbabilityTheory.monotone_cdf μ hyx
        exact (not_lt_of_ge hy) (lt_of_le_of_lt hmono hlt)
      have he : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hclosed : IsClosed (Set.Ici u) := isClosed_Ici
    exact hclosed.mem_of_tendsto hFseq (Filter.Eventually.of_forall hvalues)
  · intro hux
    exact csInf_le hbounded hux

/-- A uniform random variable on `(0,1)`, using unnormalized Lebesgue restriction (whose total
mass is one). -/
noncomputable def uniformOpenUnit : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Ioo 0 1)

instance isProbabilityMeasure_uniformOpenUnit : IsProbabilityMeasure uniformOpenUnit := by
  refine ⟨?_⟩
  simp [uniformOpenUnit, Real.volume_Ioo]

/-- Applying the generalized quantile of a probability law to a uniform level has that law. -/
theorem cdfGeneralizedQuantile_map_uniformOpenUnit
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (uniformOpenUnit).map (fun u => cdfGeneralizedQuantile
      (ProbabilityTheory.cdf μ) u) = μ := by
  let Q  := fun u => cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u
  have hQ : AEMeasurable Q uniformOpenUnit := by
    simpa [Q, uniformOpenUnit] using aemeasurable_cdfGeneralizedQuantile_Ioo μ
  apply Measure.ext_of_Iic
  intro x
  have hset : (Q ⁻¹' Set.Iic x) ∩ Set.Ioo 0 1 =
      Set.Ioc 0 (ProbabilityTheory.cdf μ x) ∩ Set.Iio 1 := by
    ext u
    constructor
    · intro hu
      exact ⟨⟨hu.right.left, (cdfGeneralizedQuantile_le_iff μ hu.right.left hu.right.right).mp hu.left⟩, hu.right.right⟩
    · exact fun hu =>
        have hu01 := ⟨hu.left.left, hu.right⟩;
        have hq := (cdfGeneralizedQuantile_le_iff μ hu01.left hu01.right).mpr hu.left.right;
        ⟨hq, hu01⟩
  calc
    (uniformOpenUnit.map Q) (Set.Iic x) =
        uniformOpenUnit (Q ⁻¹' Set.Iic x) :=
      Measure.map_apply_of_aemeasurable hQ measurableSet_Iic
    _ = (volume : Measure ℝ) ((Q ⁻¹' Set.Iic x) ∩ Set.Ioo 0 1) := by
      rw [uniformOpenUnit, Measure.restrict_apply' measurableSet_Ioo]
    _ = (volume : Measure ℝ)
        (Set.Ioc 0 (ProbabilityTheory.cdf μ x) ∩ Set.Iio 1) := by rw [hset]
    _ = ENNReal.ofReal (ProbabilityTheory.cdf μ x) := by
      by_cases hF : ProbabilityTheory.cdf μ x < 1
      · have hsub : Set.Ioc 0 (ProbabilityTheory.cdf μ x) ⊆ Set.Iio 1 := by
          intro y hy
          exact lt_of_le_of_lt hy.2 hF
        rw [Set.inter_eq_left.mpr hsub, Real.volume_Ioc]
        simp
      · have hFone  :=
          le_antisymm (ProbabilityTheory.cdf_le_one μ x) (le_of_not_gt hF)
        rw [hFone]
        have hset' : Set.Ioc (0 : ℝ) 1 ∩ Set.Iio 1 =
            Set.Ioc 0 1 \ {1} := by
          grind
        rw [hset', measure_sdiff_null']
        simp
        · simp [Set.mem_Ioc]
    _ = μ (Set.Iic x) := ProbabilityTheory.ofReal_cdf μ x

/-- The entrance-density quantile sampler pushes uniform levels to the explicit entrance law. -/
theorem conditionedPositiveEntranceQuantile_map_uniformOpenUnit
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) :
    (uniformOpenUnit).map (fun u => cdfGeneralizedQuantile
      (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t)) u) =
        conditionedPositiveEntranceMeasure ν t := by
  let  :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure ν t hν ht
  apply cdfGeneralizedQuantile_map_uniformOpenUnit <;> assumption

/-- The transition-kernel quantile sampler pushes uniform levels to the explicit conditioned
transition law. -/
theorem conditionedPositiveTransitionQuantile_map_uniformOpenUnit
    {ν t x : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) :
    (uniformOpenUnit).map (conditionedTransitionQuantile ν t x) =
      conditionedPositiveTransitionMeasure ν t x := by
  let  :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  apply cdfGeneralizedQuantile_map_uniformOpenUnit

end DOZZ.Proofs

end
