/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module
public import Mathlib

public import PottsDiscontinuity.FK.FreeBoxLimitV1

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK.Internal

noncomputable section



theorem boxConfiguration_mono (c : LatticeVertex) (r : ℕ)
    {A B : Configuration (boxGraph c r)} (hAB : A ≤ B) :
    boxConfiguration c r A ≤ boxConfiguration c r B := by
  
  
  intro e
  by_cases hA : e ∈ A.map (boxEdgeEmbedding c r)
  · 
    simp [boxConfiguration, hA, (((Finset.map_subset_map).2 hAB) hA)]
  · simp [boxConfiguration, hA]

section

variable (q : Parameters) (c : LatticeVertex) (r : ℕ)


private theorem boxProbabilityMeasure_apply_preimage  (s : Set LatticeConfiguration)
    (hs : MeasurableSet s) :
    (boxProbabilityMeasure q c r : Measure LatticeConfiguration) s =
      measure (boxGraph c r) q (BoundaryCondition.free ∅)
        {A | boxConfiguration c r A ∈ s} := by
  change ((law (boxGraph c r) q (BoundaryCondition.free ∅)).map
    (boxConfiguration c r)).toMeasure s = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hs]
  rfl

private theorem boxProbabilityMeasure_finite_positive_association
    
    (s t : Set LatticeConfiguration) (hsUpper : IsUpperSet s)
    (htUpper : IsUpperSet t) (hsMeas : MeasurableSet s) (htMeas : MeasurableSet t) :
    (boxProbabilityMeasure q c r : Measure LatticeConfiguration).real s *
      (boxProbabilityMeasure q c r : Measure LatticeConfiguration).real t ≤
        (boxProbabilityMeasure q c r : Measure LatticeConfiguration).real (s ∩ t) := by
  let sbox  :=
    {A | boxConfiguration c r A ∈ s}
  let tbox  :=
    {A | boxConfiguration c r A ∈ t}
  
  
  have h := measure_positive_association q (BoundaryCondition.free ∅) sbox tbox (fun ⦃A B⦄ hAB => hsUpper (boxConfiguration_mono c r hAB))  fun ⦃A B⦄ hAB => htUpper (boxConfiguration_mono c r hAB) 
  
  
  
  
  rw [Measure.real_def, Measure.real_def, Measure.real_def]
  rw [ boxProbabilityMeasure_apply_preimage q c r s hsMeas ,  boxProbabilityMeasure_apply_preimage q c r t htMeas ,  boxProbabilityMeasure_apply_preimage q c r (s ∩ t) (hsMeas.inter htMeas) ]
  
  exact h

end

set_option maxHeartbeats 800000 in
/-- Positive association under the unique free-box law for any two increasing clopen events of the original lattice configuration space. -/
theorem freeBoxLimit_clopen_positive_association (q : Parameters)
    (s t : Set LatticeConfiguration) (hsClopen : IsClopen s)
    (htClopen : IsClopen t) (hsUpper : IsUpperSet s) (htUpper : IsUpperSet t) :
    (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q) s : ℝ) *
      (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q) t : ℝ) ≤
        (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q) (s ∩ t) : ℝ) := by
  let μ  :=
    Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)
  have hweak  :=
    (Classical.choose_spec (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)).1
      (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
  
  
  
  
  
  
  
  
  have hlimit := le_of_tendsto_of_tendsto' (((NNReal.continuous_coe.continuousAt.tendsto).comp (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak hsClopen)).mul ((NNReal.continuous_coe.continuousAt.tendsto).comp (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak htClopen))) ((NNReal.continuous_coe.continuousAt.tendsto).comp (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak
                                                                                                                         (hsClopen.inter htClopen)))  fun (n : ℕ) => by
                                                            have h := boxProbabilityMeasure_finite_positive_association q (0, 0) n s t
                                                              hsUpper htUpper hsClopen.2.measurableSet htClopen.2.measurableSet
                                                            all_goals simp_all 
  simpa [μ] using hlimit

end
end PottsDiscontinuity.FK.Internal
