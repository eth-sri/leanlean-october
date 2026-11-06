/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedEntranceFiniteChain
public import DOZZ.Brownian.Coupling.RationalExtension

/-!
# Joint entrance chains on a shared finite uniform grid

All drift coordinates use the same fresh uniform at each step. The resulting joint probability
law has exactly the previously constructed entrance/transition chain as each marginal; no
independence of the drift coordinates is introduced. The common-uniform inequalities hold on one
event for all the countably many drift coordinates and all grid times.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology Classical
attribute [local instance] Measure.Subtype.measureSpace

namespace DOZZ.Proofs

abbrev CoupledEntranceGridPath (J : Type*) (n : ℕ) := J → ConditionedEntranceGridPath n

/-- The shared scalar driving input is uniform on the open unit interval. -/
theorem coupling_unitInput_isProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure ConditionedUnitInput) := by
  constructor
  calc
    (volume : Measure ConditionedUnitInput) univ =
        ((volume : Measure ConditionedUnitInput).map Subtype.val) univ := by
      rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
      simp
    _ = uniformOpenUnit univ := by rw [(show (volume : Measure ConditionedUnitInput).map Subtype.val = uniformOpenUnit by rw [MeasurableSet.map_coe_volume measurableSet_Ioo, uniformOpenUnit])]
    _ = 1 := by simp [uniformOpenUnit, Real.volume_Ioo]

/-- The first states at all drifts, sampled with one common uniform variable. -/
noncomputable def coupledEntranceGridInitial {J : Type*}
    (v : J → ℝ≥0) (t₀ : ℝ) (ht₀ : 0 < t₀) (u : ConditionedUnitInput) :
    CoupledEntranceGridPath J 0 :=
  fun j _ => conditionedPositiveEntranceQuantileOnSubtype (v j) t₀ (NNReal.coe_nonneg (v j)) ht₀ u

theorem measurable_coupledEntranceGridInitial {J : Type*}
    (v : J → ℝ≥0) t₀ (ht₀ : 0 < t₀) :
    Measurable (coupledEntranceGridInitial v t₀ ht₀) := by
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_conditionedPositiveEntranceQuantileWalkOn
    (v j) t₀ (fun _ => 1) (NNReal.coe_nonneg (v j)) ht₀ (fun _ => by norm_num) 0).comp (measurable_pi_iff.mpr fun _ => measurable_id)

/-- Append each coordinate's explicit transition quantile using the same new uniform. -/
noncomputable def coupledEntranceGridAppend {J : Type*}
    (v : J → ℝ≥0) (dt : ℕ → ℝ) (hdt : ∀ n, 0 < dt n) (n : ℕ)
    (z : CoupledEntranceGridPath J n × ConditionedUnitInput) :
    CoupledEntranceGridPath J (n + 1) :=
  fun j => conditionedPositiveEntranceGridAppend (v j) dt (NNReal.coe_nonneg (v j)) hdt n (z.1 j, z.2)


theorem measurable_coupledEntranceGridAppend {J : Type*}
    (v : J → ℝ≥0) (dt : ℕ → ℝ) (hdt : ∀ n, 0 < dt n) n :
    Measurable (coupledEntranceGridAppend v dt hdt n) := by
  have coupling_measurable_scalarAppend ν (hν : 0 ≤ ν) (dt : ℕ → ℝ) (hdt : ∀ n, 0 < dt n) n : Measurable (conditionedPositiveEntranceGridAppend ν dt hν hdt n) := by
    apply measurable_pi_iff.mpr
    intro i
    induction i using Fin.lastCases with
    | last =>
        rw [(show (fun z : ConditionedEntranceGridPath n × ConditionedUnitInput => conditionedPositiveEntranceGridAppend ν dt hν hdt n z (Fin.last (n + 1))) = (fun z => conditionedPositiveEntranceGridStep ν dt hν hdt n z.1 z.2) by funext z; exact conditionedPositiveEntranceGridAppend_last ν dt hν hdt n z)]
        exact (((measurable_conditionedTransitionQuantileOn ν (dt n) hν (hdt n)).subtype_mk (h := fun z => conditionedPositiveTransitionQuantile_pos hν (hdt n) z.1.2 z.2.2.1 z.2.2.2)).comp (((measurable_pi_apply (Fin.last n)).comp measurable_fst).prodMk measurable_snd))
    | cast i =>
        rw [(show (fun z : ConditionedEntranceGridPath n × ConditionedUnitInput => conditionedPositiveEntranceGridAppend ν dt hν hdt n z i.castSucc) = (fun z => z.1 i) by funext z; exact conditionedPositiveEntranceGridAppend_castSucc ν dt hν hdt n z i)]
        exact (measurable_pi_apply i).comp measurable_fst
  apply measurable_pi_iff.mpr
  intro j
  exact (coupling_measurable_scalarAppend (v j) (NNReal.coe_nonneg (v j)) dt hdt n).comp (((measurable_pi_apply j).comp measurable_fst).prodMk measurable_snd)

/-- The actual joint finite-grid law, built by ordinary finite product extensions. -/
noncomputable def coupledEntranceGridMeasure {J : Type*}
    (v : J → ℝ≥0) (t₀ : ℝ) (dt : ℕ → ℝ) (ht₀ : 0 < t₀) (hdt : ∀ n, 0 < dt n) :
    (n : ℕ) → Measure (CoupledEntranceGridPath J n)
  | 0 => (volume : Measure ConditionedUnitInput).map (coupledEntranceGridInitial v t₀ ht₀)
  | n + 1 => ((coupledEntranceGridMeasure v t₀ dt ht₀ hdt n).prod
      (volume : Measure ConditionedUnitInput)).map (coupledEntranceGridAppend v dt hdt n)

/-- Every joint grid stage is a probability law, with no path-law existence premise. -/
theorem coupledEntranceGridMeasure_isProbabilityMeasure {J : Type*}
    (v : J → ℝ≥0) t₀ (dt : ℕ → ℝ) (ht₀ : 0 < t₀) (hdt : ∀ n, 0 < dt n)
    n : IsProbabilityMeasure (coupledEntranceGridMeasure v t₀ dt ht₀ hdt n) := by
  let _ := coupling_unitInput_isProbabilityMeasure
  induction n with
  | zero =>
      exact (Measure.isProbabilityMeasure_map_iff
        (measurable_coupledEntranceGridInitial v t₀ ht₀).aemeasurable).mpr inferInstance
  | succ n ih =>
      let _ := ih
      exact (Measure.isProbabilityMeasure_map_iff
        (measurable_coupledEntranceGridAppend v dt hdt n).aemeasurable).mpr inferInstance

/-- A coordinate marginal is exactly the previously constructed entrance/transition chain. -/
theorem coupledEntranceGridMeasure_coordinate_map {J : Type*}
    (v : J → ℝ≥0) t₀ (dt : ℕ → ℝ) (ht₀ : 0 < t₀) (hdt : ∀ n, 0 < dt n)
    j n :
    (coupledEntranceGridMeasure v t₀ dt ht₀ hdt n).map (fun x => x j) =
      conditionedPositiveEntranceGridMeasure (v j) t₀ dt (NNReal.coe_nonneg (v j)) ht₀ hdt n := by
  let _ := coupling_unitInput_isProbabilityMeasure
  induction n with
  | zero =>
      rw [coupledEntranceGridMeasure,
        Measure.map_map (measurable_pi_apply j) (measurable_coupledEntranceGridInitial v t₀ ht₀)]
      rfl
  | succ n ih =>
      let μ := coupledEntranceGridMeasure v t₀ dt ht₀ hdt n
      let U : Measure ConditionedUnitInput := volume
      let _ : IsProbabilityMeasure μ :=
        coupledEntranceGridMeasure_isProbabilityMeasure v t₀ dt ht₀ hdt n
      rw [coupledEntranceGridMeasure,
        Measure.map_map (measurable_pi_apply j) (measurable_coupledEntranceGridAppend v dt hdt n)]
      change (μ.prod U).map
        (conditionedPositiveEntranceGridAppend (v j) dt (NNReal.coe_nonneg (v j)) hdt n ∘
          (fun z => (z.1 j, z.2))) = _
      rw [← Measure.map_map (show Measurable (conditionedPositiveEntranceGridAppend (v j) dt (NNReal.coe_nonneg (v j)) hdt n) by exact (measurable_pi_apply ()).comp ((measurable_coupledEntranceGridAppend (fun _ => v j) dt hdt n).comp ((measurable_pi_iff.mpr fun _ => measurable_fst).prodMk measurable_snd))) (((measurable_pi_apply j).comp measurable_fst).prodMk measurable_snd), (show (μ.prod U).map (fun z => (z.1 j, z.2)) = (μ.map (fun x => x j)).prod U by change (μ.prod U).map (Prod.map (fun x => x j) id) = _; rw [← Measure.map_prod_map μ U (measurable_pi_apply j) measurable_id, Measure.map_id])]
      change ((coupledEntranceGridMeasure v t₀ dt ht₀ hdt n).map (fun x => x j) |>.prod U).map
        (conditionedPositiveEntranceGridAppend (v j) dt (NNReal.coe_nonneg (v j)) hdt n) = _
      rw [ih]
      rfl

/-- Elapsed time at a grid coordinate, including the first entrance sampling time. -/
def coupledEntranceGridTime (t₀ : ℝ) (dt : ℕ → ℝ) (n : ℕ) : ℝ :=
  t₀ + ∑ k ∈ Finset.range n, dt k


/-- The joint order set on the sampled positive paths. -/
def coupledEntranceGridOrderSet {J : Type*} (v : J → ℝ≥0) (t₀ : ℝ) (dt : ℕ → ℝ)
    (n : ℕ) : Set (CoupledEntranceGridPath J n) :=
  {x | ∀ j k, v j ≤ v k → ∀ i : Fin (n + 1),
    (x j i).1 ≤ (x k i).1 ∧ (x k i).1 ≤
      (x j i).1 + ((v k : ℝ) - (v j : ℝ)) * coupledEntranceGridTime t₀ dt i.1}

/-- The finite-grid constraints are closed in the countable product of finite path carriers. -/
theorem isClosed_coupledEntranceGridOrderSet {J : Type*}
    (v : J → ℝ≥0) t₀ (dt : ℕ → ℝ) (n : ℕ) :
    IsClosed (coupledEntranceGridOrderSet v t₀ dt n) := by
  simp only [coupledEntranceGridOrderSet, ofPred_forall]
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro i
  have hj : Continuous (fun x : CoupledEntranceGridPath J n => (x j i).1) :=
    continuous_subtype_val.comp ((continuous_apply i).comp (continuous_apply j))
  have hk : Continuous (fun x : CoupledEntranceGridPath J n => (x k i).1) :=
    continuous_subtype_val.comp ((continuous_apply i).comp (continuous_apply k))
  exact (isClosed_le hj hk).inter (isClosed_le hk (hj.add continuous_const))


/-- A shared transition preserves the drift order and adds only drift gap times elapsed time. -/
theorem coupledEntranceGridAppend_mem_orderSet {J : Type*}
    (v : J → ℝ≥0) t₀ (dt : ℕ → ℝ) (hdt : ∀ n, 0 < dt n) n
    x u
    (hx : x ∈ coupledEntranceGridOrderSet v t₀ dt n) :
    coupledEntranceGridAppend v dt hdt n (x, u) ∈ coupledEntranceGridOrderSet v t₀ dt (n + 1) := by
  have coupledEntranceGridTime_succ t₀ (dt : ℕ → ℝ) n : coupledEntranceGridTime t₀ dt (n + 1) = coupledEntranceGridTime t₀ dt n + dt n := by
    simp only [coupledEntranceGridTime, Finset.sum_range_succ]
    ring
  intro j k hjk i
  induction i using Fin.lastCases with
  | cast i =>
      dsimp only [coupledEntranceGridAppend]
      change (conditionedPositiveEntranceGridAppend (v j) dt (NNReal.coe_nonneg (v j)) hdt n (x j, u)
          i.castSucc).1 ≤ _ ∧ _
      rw [conditionedPositiveEntranceGridAppend_castSucc,
        conditionedPositiveEntranceGridAppend_castSucc]
      exact hx j k hjk i
  | last =>
      have hprev := hx j k hjk (Fin.last n)
      have hij : (v j : ℝ) ≤ (v k : ℝ) := hjk
      have := conditionedTransitionQuantile_start_add (NNReal.coe_nonneg (v k)) (hdt n)
        (x j (Fin.last n)).2 hprev.1 u.2.1 u.2.2
      have := conditionedTransitionQuantile_drift_add (NNReal.coe_nonneg (v j)) hij (hdt n)
        (x j (Fin.last n)).2 u.2.1 u.2.2
      dsimp only [coupledEntranceGridAppend]
      change (conditionedPositiveEntranceGridAppend (v j) dt (NNReal.coe_nonneg (v j)) hdt n (x j, u)
          (Fin.last (n + 1))).1 ≤ _ ∧ _
      rw [conditionedPositiveEntranceGridAppend_last, conditionedPositiveEntranceGridAppend_last]
      change conditionedTransitionQuantile (v j) (dt n) (x j (Fin.last n)).1 u.1 ≤
          conditionedTransitionQuantile (v k) (dt n) (x k (Fin.last n)).1 u.1 ∧
        conditionedTransitionQuantile (v k) (dt n) (x k (Fin.last n)).1 u.1 ≤
          conditionedTransitionQuantile (v j) (dt n) (x j (Fin.last n)).1 u.1 +
            ((v k : ℝ) - (v j : ℝ)) * coupledEntranceGridTime t₀ dt (n + 1)
      rw [coupledEntranceGridTime_succ]
      refine ⟨(conditionedTransitionQuantile_drift_mono (NNReal.coe_nonneg (v j)) hij (hdt n) (x j (Fin.last n)).2 u.2.1 u.2.2).trans (conditionedTransitionQuantile_start_mono (NNReal.coe_nonneg (v k)) (hdt n) (x j (Fin.last n)).2 hprev.1 u.2.1 u.2.2), ?_⟩
      simp only [Fin.val_last] at hprev
      nlinarith [hprev.2]

/-- One common full-probability event carries every drift pair and every finite grid coordinate. -/
theorem coupledEntranceGridMeasure_order_ae {J : Type*} [Countable J]
    (v : J → ℝ≥0) t₀ (dt : ℕ → ℝ) (ht₀ : 0 < t₀) (hdt : ∀ n, 0 < dt n)
    n :
    ∀ᵐ x ∂coupledEntranceGridMeasure v t₀ dt ht₀ hdt n,
      x ∈ coupledEntranceGridOrderSet v t₀ dt n := by
  have coupledEntranceGridInitial_mem_orderSet u : coupledEntranceGridInitial v t₀ ht₀ u ∈ coupledEntranceGridOrderSet v t₀ dt 0 := by
    intro j k hjk i
    have hij := hjk
    change cdfGeneralizedQuantile (cdf (conditionedPositiveEntranceMeasure (v j) t₀)) u.1 ≤
        cdfGeneralizedQuantile (cdf (conditionedPositiveEntranceMeasure (v k) t₀)) u.1 ∧
      cdfGeneralizedQuantile (cdf (conditionedPositiveEntranceMeasure (v k) t₀)) u.1 ≤
        cdfGeneralizedQuantile (cdf (conditionedPositiveEntranceMeasure (v j) t₀)) u.1 +
          ((v k : ℝ) - (v j : ℝ)) * coupledEntranceGridTime t₀ dt i.1
    rw [(show coupledEntranceGridTime t₀ dt i.1 = t₀ by rw [Fin.eq_zero i]; simp [coupledEntranceGridTime])]
    exact ⟨(conditionedPositiveEntranceQuantile_drift_le (NNReal.coe_nonneg (v j)) hij ht₀ u.2.1 u.2.2), (conditionedPositiveEntranceQuantile_drift_add (NNReal.coe_nonneg (v j)) hij ht₀ u.2.1 u.2.2)⟩
  let _ := coupling_unitInput_isProbabilityMeasure
  induction n with
  | zero =>
      apply (ae_map_iff (measurable_coupledEntranceGridInitial v t₀ ht₀).aemeasurable
        (isClosed_coupledEntranceGridOrderSet v t₀ dt 0).measurableSet).mpr
      exact ae_of_all _ (coupledEntranceGridInitial_mem_orderSet)
  | succ n ih =>
      apply (ae_map_iff (measurable_coupledEntranceGridAppend v dt hdt n).aemeasurable
        (isClosed_coupledEntranceGridOrderSet v t₀ dt (n + 1)).measurableSet).mpr
      exact ((measurePreserving_fst (μ := coupledEntranceGridMeasure v t₀ dt ht₀ hdt n) (ν := (volume : Measure ConditionedUnitInput))).quasiMeasurePreserving.ae ih).mono fun z hz => coupledEntranceGridAppend_mem_orderSet v t₀ dt hdt n z.1 z.2 hz

end DOZZ.Proofs
