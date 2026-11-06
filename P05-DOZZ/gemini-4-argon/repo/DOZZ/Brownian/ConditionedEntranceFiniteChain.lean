/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedQuantileMarkovStep
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite entrance chains driven by fresh uniform coordinates

Build each finite conditioned entrance chain by adding one independent uniform coordinate at a
time. The resulting finite path measures satisfy the deterministic-grid Markov rectangle formula
at every step; no countable product or path-space extension is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
attribute [local instance] Measure.Subtype.measureSpace

namespace DOZZ.Proofs

abbrev ConditionedUnitInput := Set.Ioo (0 : ℝ) 1
abbrev ConditionedPositiveState := Set.Ioi (0 : ℝ)
abbrev ConditionedEntranceGridPath (n : ℕ) := Fin (n + 1) → ConditionedPositiveState


/-- The entrance quantile as a positive subtype-valued function of one uniform input. -/
noncomputable def conditionedPositiveEntranceQuantileOnSubtype
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 < t) (u : ConditionedUnitInput) :
    ConditionedPositiveState :=
  ⟨cdfGeneralizedQuantile
      (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t)) u.1,
    conditionedPositiveEntranceQuantile_pos hν ht u.2.1 u.2.2⟩


/-- One fresh uniform input produces the positive subtype version of the explicit transition
quantile. -/
noncomputable def conditionedPositiveTransitionQuantileOnSubtype
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 < t) (x : ConditionedPositiveState)
    (u : ConditionedUnitInput) : ConditionedPositiveState :=
  ⟨conditionedTransitionQuantile ν t x.1 u.1,
    conditionedPositiveTransitionQuantile_pos hν ht x.2 u.2.1 u.2.2⟩

/-- The jointly measurable positive-subtype transition sampler in its start and uniform input. -/
noncomputable def conditionedPositiveTransitionQuantilePairOnSubtype
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 < t)
    (z : ConditionedPositiveState × ConditionedUnitInput) : ConditionedPositiveState :=
  ⟨conditionedTransitionQuantile ν t z.1.1 z.2.1,
    conditionedPositiveTransitionQuantile_pos hν ht z.1.2 z.2.2.1 z.2.2.2⟩

private theorem measurable_conditionedPositiveTransitionQuantilePairOnSubtype
    ν t (hν : 0 ≤ ν) (ht : 0 < t) :
    Measurable (conditionedPositiveTransitionQuantilePairOnSubtype ν t hν ht) := by
  exact (measurable_conditionedTransitionQuantileOn ν t hν ht).subtype_mk (h := fun z =>
    conditionedPositiveTransitionQuantile_pos hν ht z.1.2 z.2.2.1 z.2.2.2)

/-- The subtype-valued transition law obtained from one fresh uniform coordinate. -/
noncomputable def conditionedPositiveTransitionSubtypeMeasure
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 < t) (x : ConditionedPositiveState) :
    Measure ConditionedPositiveState :=
  (volume : Measure ConditionedUnitInput).map
    (conditionedPositiveTransitionQuantileOnSubtype ν t hν ht x)

/-- Forgetting the positive subtype recovers the explicit Doob transition probability measure. -/
theorem conditionedPositiveTransitionSubtypeMeasure_map_coe
    ν t (hν : 0 ≤ ν) (ht : 0 < t) (x : ConditionedPositiveState) :
    (conditionedPositiveTransitionSubtypeMeasure ν t hν ht x).map Subtype.val =
      conditionedPositiveTransitionMeasure ν t x.1 := by
  rw [conditionedPositiveTransitionSubtypeMeasure,
    Measure.map_map measurable_subtype_coe
      (by change Measurable (fun u => conditionedPositiveTransitionQuantilePairOnSubtype ν t hν ht (x, u)); exact ((measurable_conditionedPositiveTransitionQuantilePairOnSubtype ν t hν ht).comp (measurable_const.prodMk measurable_id)))]
  change (volume : Measure ConditionedUnitInput).map
      (fun u => conditionedTransitionQuantile ν t x.1 u.1) = _
  exact conditionedPositiveTransitionQuantile_map_uniformSubtype hν ht x

/-- Add the next transition state to a finite positive path. -/
noncomputable def conditionedPositiveEntranceGridStep
    (ν : ℝ) (dt : ℕ → ℝ) (hν : 0 ≤ ν) (hdt : ∀ n, 0 < dt n)
    (n : ℕ) (x : ConditionedEntranceGridPath n) (u : ConditionedUnitInput) :
    ConditionedPositiveState :=
  conditionedPositiveTransitionQuantilePairOnSubtype ν (dt n) hν (hdt n)
    (x (Fin.last n), u)


/-- Append one positive state to a finite grid path. -/
noncomputable def conditionedPositiveEntranceGridAppend
    (ν : ℝ) (dt : ℕ → ℝ) (hν : 0 ≤ ν) (hdt : ∀ n, 0 < dt n)
    (n : ℕ) (z : ConditionedEntranceGridPath n × ConditionedUnitInput) :
    ConditionedEntranceGridPath (n + 1) :=
  fun i => Fin.lastCases
    (conditionedPositiveEntranceGridStep ν dt hν hdt n z.1 z.2) z.1 i

theorem conditionedPositiveEntranceGridAppend_last
    ν (dt : ℕ → ℝ) (hν : 0 ≤ ν) (hdt : ∀ n, 0 < dt n)
    n (z : ConditionedEntranceGridPath n × ConditionedUnitInput) :
    conditionedPositiveEntranceGridAppend ν dt hν hdt n z (Fin.last (n + 1)) =
      conditionedPositiveEntranceGridStep ν dt hν hdt n z.1 z.2 := by
  simp [conditionedPositiveEntranceGridAppend, Fin.lastCases_last]

theorem conditionedPositiveEntranceGridAppend_castSucc
    ν (dt : ℕ → ℝ) (hν : 0 ≤ ν) (hdt : ∀ n, 0 < dt n)
    n (z : ConditionedEntranceGridPath n × ConditionedUnitInput)
    (i : Fin (n + 1)) :
    conditionedPositiveEntranceGridAppend ν dt hν hdt n z i.castSucc = z.1 i := by
  simp [conditionedPositiveEntranceGridAppend, Fin.lastCases_castSucc]

/-- The finite path law is defined recursively by adding one independent uniform coordinate and
applying the explicit entrance or transition quantile. -/
noncomputable def conditionedPositiveEntranceGridMeasure
    (ν t₀ : ℝ) (dt : ℕ → ℝ) (hν : 0 ≤ ν) (ht₀ : 0 < t₀)
    (hdt : ∀ n, 0 < dt n) :
    (n : ℕ) → Measure (ConditionedEntranceGridPath n)
  | 0 => (volume : Measure ConditionedUnitInput).map (fun u =>
      fun _ : Fin 1 => conditionedPositiveEntranceQuantileOnSubtype ν t₀ hν ht₀ u)
  | n + 1 =>
      ((conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt n).prod
        (volume : Measure ConditionedUnitInput)).map (fun z =>
          conditionedPositiveEntranceGridAppend ν dt hν hdt n z)





/-- The base coordinate of the finite entrance chain has the entrance law. -/
theorem conditionedPositiveEntranceGridMeasure_initial_law
    ν t₀ (dt : ℕ → ℝ) (hν : 0 ≤ ν) (ht₀ : 0 < t₀)
    (hdt : ∀ n, 0 < dt n) :
      (conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt 0).map
  (fun p => (p 0).1) = conditionedPositiveEntranceMeasure ν t₀ := by
  have conditionedPositiveEntranceGridMeasure_zero ν t₀ (dt : ℕ → ℝ) (hν : 0 ≤ ν) (ht₀ : 0 < t₀) (hdt : ∀ n, 0 < dt n) : conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt 0 = (volume : Measure ConditionedUnitInput).map (fun u => fun _ : Fin 1 => conditionedPositiveEntranceQuantileOnSubtype ν t₀ hν ht₀ u) := rfl
  have measurable_conditionedPositiveEntranceQuantileOnSubtype t (hν : 0 ≤ ν) (ht : 0 < t) : Measurable (conditionedPositiveEntranceQuantileOnSubtype ν t hν ht) := by
    let μ := conditionedPositiveEntranceMeasure ν t
    let : IsProbabilityMeasure μ := isProbabilityMeasure_conditionedPositiveEntranceMeasure
      ν t hν ht
    have hreal : Measurable (fun u : ConditionedUnitInput =>
        cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u.1) := by
      apply Monotone.measurable
      intro u v huv
      exact cdfGeneralizedQuantile_monoOn_Ioo μ u.2 v.2 huv
    exact hreal.subtype_mk (h := fun u =>
      conditionedPositiveEntranceQuantile_pos hν ht u.2.1 u.2.2)
  rw [conditionedPositiveEntranceGridMeasure_zero]
  have hbase : Measurable (fun u =>
      fun _ : Fin 1 => conditionedPositiveEntranceQuantileOnSubtype ν t₀ hν ht₀ u) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_conditionedPositiveEntranceQuantileOnSubtype t₀ hν ht₀
  rw [Measure.map_map (show Measurable (fun p => (p 0).1) by exact measurable_subtype_coe.comp (measurable_pi_apply 0)) hbase]
  change (volume : Measure ConditionedUnitInput).map
      (fun u => (conditionedPositiveEntranceQuantileOnSubtype ν t₀ hν ht₀ u).1) = _
  rw [← (show (fun u => (conditionedPositiveEntranceQuantileWalkOn ν t₀ dt (fun _ => u) hν ht₀ hdt 0).1) = (fun u => (conditionedPositiveEntranceQuantileOnSubtype ν t₀ hν ht₀ u).1) by funext u; rfl)]
  exact conditionedPositiveEntranceQuantileWalkOn_initial_law ν t₀ dt hν ht₀ hdt

/-- At every deterministic grid step, the finite entrance-chain law satisfies the Markov
rectangle formula with the explicit positive Doob transition kernel. -/
theorem conditionedPositiveEntranceGridMeasure_markov_rect
    (ν t₀ : ℝ) (dt : ℕ → ℝ) (hν : 0 ≤ ν) (ht₀ : 0 < t₀)
    (hdt : ∀ n, 0 < dt n) (n : ℕ)
    A B
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt (n + 1)).map
      (fun p => (Fin.init p, p (Fin.last (n + 1))))) (A ×ˢ B) =
        ∫⁻ x in A,
          conditionedPositiveTransitionSubtypeMeasure ν (dt n) hν (hdt n)
            (x (Fin.last n)) B ∂
          conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt n := by
  have measurable_conditionedPositiveEntranceGridStep : Measurable (fun z : ConditionedEntranceGridPath n × ConditionedUnitInput => conditionedPositiveEntranceGridStep ν dt hν hdt n z.1 z.2) := (measurable_conditionedPositiveTransitionQuantilePairOnSubtype ν (dt n) hν (hdt n)).comp ((measurable_pi_apply (Fin.last n)).comp measurable_fst |>.prodMk
      measurable_snd)
  have measurable_conditionedPositiveEntranceGridAppend : Measurable (fun z : ConditionedEntranceGridPath n × ConditionedUnitInput => conditionedPositiveEntranceGridAppend ν dt hν hdt n z) := by
    apply measurable_pi_iff.mpr
    intro i
    induction i using Fin.lastCases with
    | last =>
        exact (by funext z; exact conditionedPositiveEntranceGridAppend_last ν dt hν hdt n z) ▸ measurable_conditionedPositiveEntranceGridStep
    | cast j =>
        exact (by funext z; exact conditionedPositiveEntranceGridAppend_castSucc ν dt hν hdt n z j) ▸ (measurable_pi_apply j).comp measurable_fst
  have conditionedPositiveEntranceGridMeasure_succ (ν : ℝ) t₀ (dt : ℕ → ℝ) (hν : 0 ≤ ν) (ht₀ : 0 < t₀) (hdt : ∀ n, 0 < dt n) n : conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt (n + 1) = ((conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt n).prod (volume : Measure ConditionedUnitInput)).map (fun z => conditionedPositiveEntranceGridAppend ν dt hν hdt n z) := rfl
  have isProbabilityMeasure_unitInput : IsProbabilityMeasure (volume : Measure ConditionedUnitInput) := by
    refine ⟨?_⟩
    calc
      (volume : Measure ConditionedUnitInput) Set.univ =
          ((volume : Measure ConditionedUnitInput).map Subtype.val) Set.univ := by
            rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
            simp
      _ = uniformOpenUnit Set.univ := by rw [(show (volume : Measure ConditionedUnitInput).map Subtype.val = uniformOpenUnit by rw [MeasurableSet.map_coe_volume measurableSet_Ioo, uniformOpenUnit])]
      _ = 1 := by simp [uniformOpenUnit, Real.volume_Ioo]
  let μ := conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt n
  let U : Measure ConditionedUnitInput := volume
  let : IsProbabilityMeasure U := isProbabilityMeasure_unitInput
  let f : ConditionedEntranceGridPath n × ConditionedUnitInput → ConditionedPositiveState := fun z =>
    conditionedPositiveEntranceGridStep ν dt hν hdt n z.1 z.2
  have hinit : Measurable (fun p : ConditionedEntranceGridPath (n + 1) => Fin.init p) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply i.castSucc
  have hcomp :
      (fun z : ConditionedEntranceGridPath n × ConditionedUnitInput =>
        (Fin.init (conditionedPositiveEntranceGridAppend ν dt hν hdt n z),
          (conditionedPositiveEntranceGridAppend ν dt hν hdt n z) (Fin.last (n + 1)))) =
      (fun z => (z.1, f z)) := by
    funext z
    apply Prod.ext
    · funext i
      change conditionedPositiveEntranceGridAppend ν dt hν hdt n z i.castSucc = z.1 i
      exact conditionedPositiveEntranceGridAppend_castSucc ν dt hν hdt n z i
    · simpa [f] using conditionedPositiveEntranceGridAppend_last ν dt hν hdt n z
  have hmap :
      (conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt (n + 1)).map
          (fun p => (Fin.init p, p (Fin.last (n + 1)))) =
        (μ.prod U).map (fun z => (z.1, f z)) := by
    rw [conditionedPositiveEntranceGridMeasure_succ]
    rw [Measure.map_map (show Measurable (fun p : ConditionedEntranceGridPath (n + 1) => (Fin.init p, p (Fin.last (n + 1)))) by exact hinit.prodMk (measurable_pi_apply (Fin.last (n + 1))))
      (measurable_conditionedPositiveEntranceGridAppend)]
    exact congrArg (fun g => (μ.prod U).map g) hcomp
  rw [hmap]
  exact map_prod_graph_apply_rect μ U f (measurable_conditionedPositiveEntranceGridStep)
    (fun x => conditionedPositiveTransitionSubtypeMeasure ν (dt n) hν (hdt n)
      (x (Fin.last n))) (by intro x; rfl) A B hA hB

end DOZZ.Proofs

end
