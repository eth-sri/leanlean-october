module

public import NearlyMinimax.AtomicRules

@[expose] public section

/-! Total variation and support of the finite signed rules. -/
noncomputable section
namespace NearlyMinimax
open scoped BigOperators ENNReal
open MeasureTheory VectorMeasure

section Atomic
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSingletonClass X]

section
variable (z : ι → X)

theorem atomicVariationBound_total  w :
    atomicVariationBound z w Set.univ = ∑ i, ‖w i‖ₑ := by
  simp [atomicVariationBound, Measure.finsetSum_apply, enorm_eq_nnnorm]

theorem atomicSignedRule_totalVariation_le  w :
    ((atomicSignedRule z w).variation Set.univ).toReal ≤ ∑ i, |w i| := by
  have h := Measure.le_iff.1 (atomicSignedRule_variation_le z w) Set.univ MeasurableSet.univ
  rw [atomicVariationBound_total] at h
  have hfin : (∑ i, ‖w i‖ₑ) ≠ ∞ := by simp
  apply (ENNReal.toReal_mono hfin h).trans_eq
  rw [ENNReal.toReal_sum (fun i hi => enorm_ne_top)]
  simp

theorem atomicSignedRule_singleton  w
    (hz : Function.Injective z) (i : ι) : atomicSignedRule z w {z i} = w i := by
  classical
  rw [atomicSignedRule, VectorMeasure.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    exact VectorMeasure.dirac_apply_of_notMem (by simpa using hz.ne hji)
  · simp

/-- Distinct atoms give equality of the actual total variation and the atom-weight sum. -/
theorem atomicSignedRule_totalVariation_eq  w
    (hz : Function.Injective z) :
    ((atomicSignedRule z w).variation Set.univ).toReal = ∑ i, |w i| := by
  classical
  have hsingleton (i : ι) : (atomicSignedRule z w).variation {z i} = ‖w i‖ₑ := by
    rw [VectorMeasure.variation_apply_singleton, atomicSignedRule_singleton z w hz i]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) (fun i => ({z i} : Set X)) := by
    simp_all
  have hsum := measure_biUnion_finset (μ := (atomicSignedRule z w).variation)
    hdisj (fun i hi => measurableSet_singleton (z i))
  have hlower : (∑ i, ‖w i‖ₑ) ≤ (atomicSignedRule z w).variation Set.univ := by
    simp_rw [hsingleton] at hsum
    rw [← hsum]
    exact measure_mono (Set.subset_univ _)
  have hupper := Measure.le_iff.1 (atomicSignedRule_variation_le z w) Set.univ MeasurableSet.univ
  rw [atomicVariationBound_total] at hupper
  have he := le_antisymm hupper hlower
  rw [he, ENNReal.toReal_sum (fun i hi => enorm_ne_top)]
  simp
end


end Atomic

section Covariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Covariance
end NearlyMinimax
