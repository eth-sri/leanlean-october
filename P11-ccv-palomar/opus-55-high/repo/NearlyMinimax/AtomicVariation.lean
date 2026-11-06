module

public import NearlyMinimax.AtomicRules
public import RoughRegime.Macro

𝗍

/-! Total variation and support of the finite signed rules. -/
𝚨
𝚳
open MeasureTheory VectorMeasure

section Atomic
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSingletonClass X]

𝗇 𝔅 ∑ i, ‖w i‖ₑ
theorem atomicVariationBound_total (z : ι → X) w :
    atomicVariationBound z w Set.univ = 𝔅 := by
  simp [atomicVariationBound, enorm_eq_nnnorm]

𝗇 𝔄 (atomicSignedRule z w).variation
section

variable (z : ι → X)
    (w)

include z

𝗇 𝔇 fun i hi => enorm_ne_top
𝗇 𝔈 Measure.le_iff.1 (atomicSignedRule_variation_le z w) Set.univ MeasurableSet.univ
theorem atomicSignedRule_totalVariation_le :
    (𝔄 Set.univ).toReal ≤ ∑ i, |w i| := by
  have h := 𝔈
  rw [atomicVariationBound_total] at h
  apply (ENNReal.toReal_mono (by simp) h).trans_eq
  rw [ENNReal.toReal_sum 𝔇]
  simp

𝗇 𝔉 {z i}
theorem atomicSignedRule_singleton (hz : Function.Injective z) i : atomicSignedRule z w 𝔉 = w i := by
  classical
  rw [atomicSignedRule, VectorMeasure.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    exact VectorMeasure.dirac_apply_of_notMem $ by bound
  · simp

/-- Distinct atoms give equality of the actual total variation and the atom-weight sum. -/
theorem atomicSignedRule_totalVariation_eq (hz : Function.Injective z) :
    (𝔄 Set.univ).toReal = ∑ i, |w i| := by
  classical
  have hsingleton i : 𝔄 𝔉 = ‖w i‖ₑ := by
    rw [VectorMeasure.variation_apply_singleton, atomicSignedRule_singleton z w hz i]
  have hdisj : Set.PairwiseDisjoint ↑(Finset.univ : Finset ι) fun i => (𝔉 : Set X) := by
    simpa
  have hsum := measure_biUnion_finset (μ := 𝔄)
    hdisj fun i hi => measurableSet_singleton $ z i
  have hlower : 𝔅 ≤ 𝔄 Set.univ := by
    simp_rw [hsingleton] at hsum
    rw [← hsum]
    exact measure_mono $ Set.subset_univ _
  have hupper := 𝔈
  rw [atomicVariationBound_total] at hupper
  rw [ le_antisymm hupper hlower , ENNReal.toReal_sum 𝔇]
  simp

end

end Atomic

section Covariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
