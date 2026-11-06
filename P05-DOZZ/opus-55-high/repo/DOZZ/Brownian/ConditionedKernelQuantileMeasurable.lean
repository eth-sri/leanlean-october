/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedQuantileSampler
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Joint measurability of conditioned transition quantiles

For fixed time and drift, the transition CDF is antitone in the positive starting state. The
generalized inverse has rationally generated strict sublevel sets, giving joint measurability in
the state and uniform input.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Topology
open scoped Topology

namespace DOZZ.Proofs

private theorem cdfGeneralizedQuantile_lt_iff_exists_rat
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {u a : ℝ}
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u < a ↔
      ∃ q : ℚ, (q : ℝ) < a ∧ u ≤ ProbabilityTheory.cdf μ q := by
  let F := ProbabilityTheory.cdf μ
  let S := {y | u ≤ F y}
  have hnonempty : S.Nonempty := by
    have hev :=
      (ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hu1)
    obtain ⟨y, hy⟩ := Filter.eventually_atTop.1 hev
    exact ⟨y, le_of_lt (hy y le_rfl)⟩
  have hbounded : BddBelow S := by
    have hev :=
      (ProbabilityTheory.tendsto_cdf_atBot μ).eventually (Iio_mem_nhds hu)
    obtain ⟨b, hb⟩ := Filter.eventually_atBot.1 hev
    refine ⟨b, ?_⟩
    intro y hy
    grind
  change sInf S < a ↔ _
  constructor
  · intro hqa
    obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hqa
    have hqF : u ≤ F q := by
      by_contra hnot
      have hlt := lt_of_not_ge hnot
      have hqLower : q ≤ sInf S := by
        apply le_csInf hnonempty
        intro y hy
        change u ≤ F y at hy
        by_contra hyq
        have hmono := ProbabilityTheory.monotone_cdf μ (le_of_lt (lt_of_not_ge hyq))
        linarith
      linarith
    tauto
  · rintro ⟨q, hqa, hqF⟩
    have hq := csInf_le hbounded hqF
    linarith

private theorem measurable_conditionedTransitionCDF_start
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (z : ℝ) :
    Measurable (fun x : Set.Ioi (0 : ℝ) =>
      ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x.1) z) := by
  apply Antitone.measurable
  intro x y hxy
  change ProbabilityTheory.cdf
      (conditionedPositiveTransitionMeasure ν t y.1) z ≤
    ProbabilityTheory.cdf _ z
  rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht y.property,
    conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht x.property]
  exact conditionedPositiveTransitionDensity_start_cdf_le
    hν ht x.property hxy z

/-- The transition quantile restricted to positive starts and uniform levels is measurable in both
arguments. -/
theorem measurable_conditionedTransitionQuantileOn
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 < t) :
    Measurable (fun z : Set.Ioi (0 : ℝ) × Set.Ioo (0 : ℝ) 1 =>
      conditionedTransitionQuantile ν t z.1.1 z.2.1) := by
  apply measurable_of_Iio
  intro a
  let E : ℚ → Set (Set.Ioi (0 : ℝ) × Set.Ioo (0 : ℝ) 1) := fun q =>
    {z | z.2.1 ≤ ProbabilityTheory.cdf
      (conditionedPositiveTransitionMeasure ν t z.1.1) q}
  have hpre : (fun z =>
      conditionedTransitionQuantile ν t z.1.1 z.2.1) ⁻¹' Set.Iio a =
        ⋃ q : {q : ℚ // q < a}, E q.1 := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, E]
    let : IsProbabilityMeasure
        (conditionedPositiveTransitionMeasure ν t z.1.1) :=
      isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t z.1.1
        hν ht z.1.2
    exact (cdfGeneralizedQuantile_lt_iff_exists_rat
      (conditionedPositiveTransitionMeasure ν t z.1.1)
      z.2.2.1 z.2.2.2).trans (by
        simp)
  rw [hpre]
  apply MeasurableSet.iUnion
  intro q
  have hpair : Measurable (fun z : Set.Ioi (0 : ℝ) × Set.Ioo (0 : ℝ) 1 =>
      (z.2.1, ProbabilityTheory.cdf
        (conditionedPositiveTransitionMeasure ν t z.1.1) q.1)) := (measurable_subtype_coe.comp measurable_snd).prodMk
      ((measurable_conditionedTransitionCDF_start hν ht q.1).comp measurable_fst)
  exact (measurableSet_le measurable_fst measurable_snd).preimage hpair

end DOZZ.Proofs

end
