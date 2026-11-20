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
variable (z : ι → X) (w : ι → ℝ)

theorem atomicVariationBound_total :
    atomicVariationBound z w Set.univ = ∑ i, ‖w i‖ₑ := by
  simp [atomicVariationBound, Measure.finsetSum_apply, enorm_eq_nnnorm]

theorem atomicSignedRule_totalVariation_le :
    ((atomicSignedRule z w).variation Set.univ).toReal ≤ ∑ i, |w i| := by
  have h := Measure.le_iff.1 (atomicSignedRule_variation_le z w) Set.univ MeasurableSet.univ
  rw [atomicVariationBound_total] at h
  apply (ENNReal.toReal_mono (by simp) h).trans_eq
  rw [ENNReal.toReal_sum (fun i hi => enorm_ne_top)]
  simp

end

variable {z : ι → X} (w : ι → ℝ) (hz : Function.Injective z)
include hz

theorem atomicSignedRule_singleton (i : ι) : atomicSignedRule z w {z i} = w i := by
  classical
  rw [atomicSignedRule, VectorMeasure.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    solve_by_elim [VectorMeasure.dirac_apply_of_notMem]
  · simp

/-- Distinct atoms give equality of the actual total variation and the atom-weight sum. -/
theorem atomicSignedRule_totalVariation_eq :
    ((atomicSignedRule z w).variation Set.univ).toReal = ∑ i, |w i| := by
  classical
  have hsingleton i : (atomicSignedRule z w).variation {z i} = ‖w i‖ₑ := by
    rw [VectorMeasure.variation_apply_singleton, atomicSignedRule_singleton w hz i]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) (fun i => ({z i} : Set X)) := fun i hi j hj hij => Set.disjoint_singleton.mpr (hz.ne hij)
  have hsum := measure_biUnion_finset (μ := (atomicSignedRule z w).variation)
    hdisj (fun i hi => measurableSet_singleton (z i))
  have hlower : (∑ i, ‖w i‖ₑ) ≤ (atomicSignedRule z w).variation Set.univ := by
    simp_rw [hsingleton] at hsum
    rw [← hsum]
    exact measure_mono (Set.subset_univ _)
  have hupper := Measure.le_iff.1 (atomicSignedRule_variation_le z w) Set.univ MeasurableSet.univ
  rw [atomicVariationBound_total] at hupper
  rw [(le_antisymm hupper hlower), ENNReal.toReal_sum (fun i hi => enorm_ne_top)]
  simp

end Atomic

section Covariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Covariance
end NearlyMinimax
