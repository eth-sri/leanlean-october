/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.FreeBoxLimit

public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK.Internal

noncomputable section

attribute [local instance] configurationMeasurableSpace

theorem boxConfiguration_mono (c : LatticeVertex) (r : ℕ)
    {A B : Configuration (boxGraph c r)} (hAB : A ≤ B) :
    boxConfiguration c r A ≤ boxConfiguration c r B := by
  have hmap : A.map (boxEdgeEmbedding c r) ⊆ B.map (boxEdgeEmbedding c r) :=
    by simp_all
  intro e
  by_cases hA : e ∈ A.map (boxEdgeEmbedding c r)
  · simp [boxConfiguration, hA, (hmap hA)]
  · simp [boxConfiguration, hA]

section
variable (q : Parameters) (c : LatticeVertex) (r : ℕ)
theorem boxProbabilityMeasure_apply_preimage (s : Set LatticeConfiguration)
    (hs : MeasurableSet s) :
    (boxProbabilityMeasure q c r : Measure LatticeConfiguration) s =
      measure (boxGraph c r) q (BoundaryCondition.free ∅)
        {A | boxConfiguration c r A ∈ s} := by
  change ((law (boxGraph c r) q (BoundaryCondition.free ∅)).map
    (boxConfiguration c r)).toMeasure s = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hs]
  rfl

theorem boxProbabilityMeasure_finite_positive_association
    (s t : Set LatticeConfiguration) (hsUpper : IsUpperSet s)
    (htUpper : IsUpperSet t) (hsMeas : MeasurableSet s) (htMeas : MeasurableSet t) :
    (boxProbabilityMeasure q c r : Measure LatticeConfiguration).real s *
      (boxProbabilityMeasure q c r : Measure LatticeConfiguration).real t ≤
        (boxProbabilityMeasure q c r : Measure LatticeConfiguration).real (s ∩ t) := by
  let sbox :=
    {A | boxConfiguration c r A ∈ s}
  let tbox :=
    {A | boxConfiguration c r A ∈ t}
  have hsbox : IsUpperSet sbox := by
    intro A B hAB hA
    exact hsUpper (boxConfiguration_mono c r hAB) hA
  have htbox : IsUpperSet tbox := by
    intro A B hAB hA
    exact htUpper (boxConfiguration_mono c r hAB) hA
  have h := measure_positive_association q (BoundaryCondition.free ∅) sbox tbox hsbox htbox
  have hS := boxProbabilityMeasure_apply_preimage q c r s hsMeas
  have hT := boxProbabilityMeasure_apply_preimage q c r t htMeas
  have hST := boxProbabilityMeasure_apply_preimage q c r (s ∩ t) (hsMeas.inter htMeas)
  have hsets : sbox ∩ tbox = {A | boxConfiguration c r A ∈ s ∩ t} := by
    rfl
  rw [Measure.real_def, Measure.real_def, Measure.real_def]
  grind
end

/-- Positive association under the unique free-box law for any two increasing clopen events of the original lattice configuration space. -/
theorem freeBoxLimit_clopen_positive_association (q : Parameters)
    (s t : Set LatticeConfiguration) (hsClopen : IsClopen s)
    (htClopen : IsClopen t) (hsUpper : IsUpperSet s) (htUpper : IsUpperSet t) :
    (Classical.choose (freeBoxLimit_existsUnique q) s : ℝ) *
      (Classical.choose (freeBoxLimit_existsUnique q) t : ℝ) ≤
        (Classical.choose (freeBoxLimit_existsUnique q) (s ∩ t) : ℝ) := by
  let μ :=
    Classical.choose (freeBoxLimit_existsUnique q)
  have hweak : Tendsto (fun n => boxProbabilityMeasure q (0, 0) n) atTop (𝓝 μ) :=
    (Classical.choose_spec (freeBoxLimit_existsUnique q)).1
      (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
  have hS :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak hsClopen
  have hT :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak htClopen
  have hST :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak
      (hsClopen.inter htClopen)
  have hSreal : Tendsto (fun n =>
      (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) s : NNReal) : ℝ)) atTop
      (𝓝 ((μ s : NNReal) : ℝ)) :=
    by simp_all
  have hTreal : Tendsto (fun n =>
      (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) t : NNReal) : ℝ)) atTop
      (𝓝 ((μ t : NNReal) : ℝ)) :=
    by simp_all
  have hSTreal : Tendsto (fun n =>
      (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) (s ∩ t) : NNReal) : ℝ)) atTop
      (𝓝 ((μ (s ∩ t) : NNReal) : ℝ)) :=
    by simp_all
  have hfinite (n : ℕ) :
      (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) s : NNReal) : ℝ) *
        (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) t : NNReal) : ℝ) ≤
          (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) (s ∩ t) : NNReal) : ℝ) := by
    have h := boxProbabilityMeasure_finite_positive_association q (0, 0) n s t
      hsUpper htUpper hsClopen.2.measurableSet htClopen.2.measurableSet
    simp_all
  have hlimit := le_of_tendsto_of_tendsto' (hSreal.mul hTreal) hSTreal hfinite
  omega

end
end PottsDiscontinuity.FK.Internal
