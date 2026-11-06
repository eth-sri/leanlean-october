/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedEntranceQuantileChainMeasurable

/-!
# One finite Markov step from an independent uniform input

This measure-theoretic lemma identifies rectangle probabilities for a sampled transition from
the one-step pushforward law. It uses an ordinary two-factor product measure; no countable product
or extension theorem is involved.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
attribute [local instance] Measure.Subtype.measureSpace

namespace DOZZ.Proofs

/-- If each fresh input `u` samples the transition law `K x`, then an independent input pair
`(x,u)` gives the Markov rectangle formula for the graph `(x,f(x,u))`. -/
theorem map_prod_graph_apply_rect
    {X U Y : Type*} [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace Y]
    (μ : Measure X) (η : Measure U) [SFinite η] (f : X × U → Y) (hf : Measurable f)
    (K : X → Measure Y)
    (hK : ∀ x, η.map (fun u => f (x, u)) = K x)
    (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (μ.prod η).map (fun z => (z.1, f z)) (A ×ˢ B) =
      ∫⁻ x in A, K x B ∂μ := by
  let F : X × U → X × Y := fun z => (z.1, f z)
  have hF  := measurable_fst.prodMk hf
  have hRect  := hA.prod hB
  have hPre  := hRect.preimage hF
  rw [Measure.map_apply hF hRect, Measure.prod_apply hPre]
  rw [← lintegral_indicator hA]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ A
  · have hfx : Measurable (fun u => f (x, u)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    have hset : Prod.mk x ⁻¹' (F ⁻¹' (A ×ˢ B)) =
        (fun u => f (x, u)) ⁻¹' B := by
      ext u
      simp [F, hx]
    rw [hset, Set.indicator_of_mem hx]
    rw [← Measure.map_apply hfx hB, hK x]
  · have hset : Prod.mk x ⁻¹' (F ⁻¹' (A ×ˢ B)) = ∅ := by
      ext u
      simp [F, hx]
    rw [hset]
    simp [hx]

/-- A fresh uniform level in the subtype `(0,1)` samples the explicit transition probability
measure from every positive start. -/
theorem conditionedPositiveTransitionQuantile_map_uniformSubtype
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (x : Set.Ioi (0 : ℝ)) :
    (volume : Measure (Set.Ioo (0 : ℝ) 1)).map
      (fun u => conditionedTransitionQuantile ν t x.1 u.1) =
        conditionedPositiveTransitionMeasure ν t x.1 := by
  let μ := conditionedPositiveTransitionMeasure ν t x.1
  let q : ℝ → ℝ := fun u =>
    cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u
  let  :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x.1 hν ht x.2
  have hqUniform : AEMeasurable q uniformOpenUnit := id (aemeasurable_cdfGeneralizedQuantile_Ioo μ)
  have hcoe :
      (volume : Measure (Set.Ioo (0 : ℝ) 1)).map Subtype.val = uniformOpenUnit := by
    rw [MeasurableSet.map_coe_volume measurableSet_Ioo, uniformOpenUnit]
  have hqMap : AEMeasurable q
      ((volume : Measure (Set.Ioo (0 : ℝ) 1)).map Subtype.val) := by
    rw [hcoe]
    exact hqUniform
  have hval : AEMeasurable (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ)
      (volume : Measure (Set.Ioo (0 : ℝ) 1)) := measurable_subtype_coe.aemeasurable
  calc
    (volume : Measure (Set.Ioo (0 : ℝ) 1)).map
        (fun u => conditionedTransitionQuantile ν t x.1 u.1) =
      ((volume : Measure (Set.Ioo (0 : ℝ) 1)).map Subtype.val).map q := (AEMeasurable.map_map_of_aemeasurable hqMap hval).symm
    _ = uniformOpenUnit.map q := by rw [hcoe]
    _ = μ := conditionedPositiveTransitionQuantile_map_uniformOpenUnit hν ht x.2

end DOZZ.Proofs

end
