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

theorem isProbabilityMeasure_unitInput :
    IsProbabilityMeasure (volume : Measure ConditionedUnitInput) := by
  refine ⟨?_⟩
  have hcoe :
      (volume : Measure ConditionedUnitInput).map Subtype.val = uniformOpenUnit := by
    rw [MeasurableSet.map_coe_volume measurableSet_Ioo, uniformOpenUnit]
  calc
    volume Set.univ =
        ((volume : Measure ConditionedUnitInput).map Subtype.val) Set.univ := by
          rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
          simp
    _ = uniformOpenUnit Set.univ := by simp_all
    _ = 1 := by simp

/-- The entrance quantile as a positive subtype-valued function of one uniform input. -/
noncomputable def conditionedPositiveEntranceQuantileOnSubtype
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 < t) (u : ConditionedUnitInput) :
    ConditionedPositiveState :=
  ⟨cdfGeneralizedQuantile
      (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t)) u.1,
    conditionedPositiveEntranceQuantile_pos hν ht u.2.1 u.2.2⟩

private theorem measurable_conditionedPositiveEntranceQuantileOnSubtype
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 < t) :
    Measurable (conditionedPositiveEntranceQuantileOnSubtype ν t hν ht) := by
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
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 < t) :
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
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 < t) (x : ConditionedPositiveState) :
    (conditionedPositiveTransitionSubtypeMeasure ν t hν ht x).map Subtype.val =
      conditionedPositiveTransitionMeasure ν t x.1 := by
  have hq : Measurable (fun u =>
      conditionedPositiveTransitionQuantilePairOnSubtype ν t hν ht (x, u)) :=
    (measurable_conditionedPositiveTransitionQuantilePairOnSubtype ν t hν ht).comp
      (measurable_const.prodMk measurable_id)
  have hq' : Measurable (conditionedPositiveTransitionQuantileOnSubtype ν t hν ht x) := by
    assumption
  rw [conditionedPositiveTransitionSubtypeMeasure,
    Measure.map_map measurable_subtype_coe
      hq']
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

private theorem measurable_conditionedPositiveEntranceGridStep
    (ν : ℝ) (dt : ℕ → ℝ) (hν : 0 ≤ ν) (hdt : ∀ n, 0 < dt n)
    (n : ℕ) :
    Measurable (fun z : ConditionedEntranceGridPath n × ConditionedUnitInput =>
      conditionedPositiveEntranceGridStep ν dt hν hdt n z.1 z.2) := by
  have hstep := measurable_conditionedPositiveTransitionQuantilePairOnSubtype
    ν (dt n) hν (hdt n)
  exact hstep.comp ((measurable_pi_apply (Fin.last n)).comp measurable_fst |>.prodMk
    measurable_snd)

/-- Append one positive state to a finite grid path. -/
noncomputable def conditionedPositiveEntranceGridAppend
    (ν : ℝ) (dt : ℕ → ℝ) (hν : 0 ≤ ν) (hdt : ∀ n, 0 < dt n)
    (n : ℕ) (z : ConditionedEntranceGridPath n × ConditionedUnitInput) :
    ConditionedEntranceGridPath (n + 1) :=
  fun i => Fin.lastCases
    (conditionedPositiveEntranceGridStep ν dt hν hdt n z.1 z.2) z.1 i
section
variable (ν : ℝ) (dt : ℕ → ℝ) (hν : 0 ≤ ν) (hdt : ∀ n, 0 < dt n) (n : ℕ) (z : ConditionedEntranceGridPath n × ConditionedUnitInput)

theorem conditionedPositiveEntranceGridAppend_last
    :
    conditionedPositiveEntranceGridAppend ν dt hν hdt n z (Fin.last (n + 1)) =
      conditionedPositiveEntranceGridStep ν dt hν hdt n z.1 z.2 := by
  simp [conditionedPositiveEntranceGridAppend, Fin.lastCases_last]

theorem conditionedPositiveEntranceGridAppend_castSucc
    (i : Fin (n + 1)) :
    conditionedPositiveEntranceGridAppend ν dt hν hdt n z i.castSucc = z.1 i := by
  simp [conditionedPositiveEntranceGridAppend, Fin.lastCases_castSucc]

end

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
section
variable (ν t₀ : ℝ) (dt : ℕ → ℝ) (hν : 0 ≤ ν) (ht₀ : 0 < t₀) (hdt : ∀ n, 0 < dt n)

theorem conditionedPositiveEntranceGridMeasure_zero
    :
    conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt 0 =
      (volume : Measure ConditionedUnitInput).map (fun u =>
        fun _ : Fin 1 => conditionedPositiveEntranceQuantileOnSubtype ν t₀ hν ht₀ u) := rfl

theorem conditionedPositiveEntranceGridMeasure_succ
    (n : ℕ) :
    conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt (n + 1) =
      ((conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt n).prod
        (volume : Measure ConditionedUnitInput)).map (fun z =>
          conditionedPositiveEntranceGridAppend ν dt hν hdt n z) := rfl

end

private theorem measurable_conditionedPositiveEntranceGridAppend
    (ν : ℝ) (dt : ℕ → ℝ) (hν : 0 ≤ ν) (hdt : ∀ n, 0 < dt n)
    (n : ℕ) :
    Measurable (fun z : ConditionedEntranceGridPath n × ConditionedUnitInput =>
      conditionedPositiveEntranceGridAppend ν dt hν hdt n z) := by
  apply measurable_pi_iff.mpr
  intro i
  induction i using Fin.lastCases with
  | last =>
      have hEq :
          (fun z =>
            conditionedPositiveEntranceGridAppend ν dt hν hdt n z (Fin.last (n + 1))) =
          (fun z => conditionedPositiveEntranceGridStep ν dt hν hdt n z.1 z.2) := by
        funext z
        exact conditionedPositiveEntranceGridAppend_last ν dt hν hdt n z
      exact hEq ▸ measurable_conditionedPositiveEntranceGridStep ν dt hν hdt n
  | cast j =>
      have hEq :
          (fun z =>
            conditionedPositiveEntranceGridAppend ν dt hν hdt n z j.castSucc) =
          (fun z => z.1 j) := by
        funext z
        exact conditionedPositiveEntranceGridAppend_castSucc ν dt hν hdt n z j
      exact hEq ▸ (measurable_pi_apply j).comp measurable_fst
section
variable (ν t₀ : ℝ) (dt : ℕ → ℝ) (hν : 0 ≤ ν) (ht₀ : 0 < t₀) (hdt : ∀ n, 0 < dt n)


/-- The base coordinate of the finite entrance chain has the entrance law. -/
theorem conditionedPositiveEntranceGridMeasure_initial_law
    :
      (conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt 0).map
  (fun p => (p 0).1) = conditionedPositiveEntranceMeasure ν t₀ := by
  rw [conditionedPositiveEntranceGridMeasure_zero]
  have hbase : Measurable (fun u : ConditionedUnitInput =>
      fun _ : Fin 1 => conditionedPositiveEntranceQuantileOnSubtype ν t₀ hν ht₀ u) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_conditionedPositiveEntranceQuantileOnSubtype ν t₀ hν ht₀
  have heval : Measurable (fun p : ConditionedEntranceGridPath 0 => (p 0).1) := by fun_prop
  rw [Measure.map_map heval hbase]
  change volume.map
      (fun u => (conditionedPositiveEntranceQuantileOnSubtype ν t₀ hν ht₀ u).1) = _
  have hfun :
      (fun u =>
        (conditionedPositiveEntranceQuantileWalkOn ν t₀ dt (fun _ => u)
          hν ht₀ hdt 0).1) =
      (fun u => (conditionedPositiveEntranceQuantileOnSubtype ν t₀ hν ht₀ u).1) := by
    rfl
  exact conditionedPositiveEntranceQuantileWalkOn_initial_law ν t₀ dt hν ht₀ hdt

/-- At every deterministic grid step, the finite entrance-chain law satisfies the Markov
rectangle formula with the explicit positive Doob transition kernel. -/
theorem conditionedPositiveEntranceGridMeasure_markov_rect
    (n : ℕ)
    (A : Set (ConditionedEntranceGridPath n)) (B : Set ConditionedPositiveState)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt (n + 1)).map
      (fun p => (Fin.init p, p (Fin.last (n + 1))))) (A ×ˢ B) =
        ∫⁻ x in A,
          conditionedPositiveTransitionSubtypeMeasure ν (dt n) hν (hdt n)
            (x (Fin.last n)) B ∂
          conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt n := by
  let μ := conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt n
  let U : Measure ConditionedUnitInput := volume
  let : IsProbabilityMeasure U := isProbabilityMeasure_unitInput
  let f : ConditionedEntranceGridPath n × ConditionedUnitInput → ConditionedPositiveState := fun z =>
    conditionedPositiveEntranceGridStep ν dt hν hdt n z.1 z.2
  have hinit : Measurable (fun p : ConditionedEntranceGridPath (n + 1) => Fin.init p) := by
    fun_prop
  have hpair : Measurable (fun p =>
      (Fin.init p, p (Fin.last (n + 1)))) := hinit.prodMk (measurable_pi_apply (Fin.last (n + 1)))
  have hcomp :
      (fun z =>
        (Fin.init (conditionedPositiveEntranceGridAppend ν dt hν hdt n z),
          (conditionedPositiveEntranceGridAppend ν dt hν hdt n z) (Fin.last (n + 1)))) =
      (fun z => (z.1, f z)) := by
    funext z
    apply Prod.ext
    · funext i
      exact conditionedPositiveEntranceGridAppend_castSucc ν dt hν hdt n z i
    · simpa [f] using conditionedPositiveEntranceGridAppend_last ν dt hν hdt n z
  have hmap :
      (conditionedPositiveEntranceGridMeasure ν t₀ dt hν ht₀ hdt _).map
          (fun p => (Fin.init p, p (Fin.last (n + 1)))) =
        (μ.prod U).map (fun z => (z.1, f z)) := by
    rw [conditionedPositiveEntranceGridMeasure_succ]
    rw [Measure.map_map hpair
      (measurable_conditionedPositiveEntranceGridAppend ν dt hν hdt n)]
    exact congrArg (fun g => (μ.prod U).map g) hcomp
  rw [hmap]
  exact map_prod_graph_apply_rect μ U f (measurable_conditionedPositiveEntranceGridStep ν dt hν hdt n)
    (fun x => conditionedPositiveTransitionSubtypeMeasure ν (dt n) hν (hdt n)
      (x (Fin.last n))) (by tauto) A B hA hB

end

end DOZZ.Proofs

end
