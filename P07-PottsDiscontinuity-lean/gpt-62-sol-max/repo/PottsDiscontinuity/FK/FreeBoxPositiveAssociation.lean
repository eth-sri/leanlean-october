/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.FreeBoxLimit

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK.Internal

noncomputable section

attribute [local instance] configurationMeasurableSpace

theorem boxConfiguration_mono (c : LatticeVertex) (r : ℕ)
    {A B : Configuration (boxGraph c r)} (hAB : A ≤ B) :
    boxConfiguration c r A ≤ boxConfiguration c r B := by
  classical
  have hmap : A.map (boxEdgeEmbedding c r) ⊆ B.map (boxEdgeEmbedding c r) :=
    (Finset.map_subset_map).2 hAB
  intro e
  by_cases hA : e ∈ A.map (boxEdgeEmbedding c r)
  · have hB := hmap hA
    simp [boxConfiguration, hA, hB]
  · simp [boxConfiguration, hA]

/-- FKG is preserved by the monotone embedding of finite-box configurations. -/
theorem boxMap_positive_association (q : Parameters) (c : LatticeVertex) (r : ℕ)
    (ξ : BoundaryCondition (BoxVertex c r)) (f : Configuration (boxGraph c r) → LatticeConfiguration)
    (hf : Monotone f) {s t : Set LatticeConfiguration}
    (hsUpper : IsUpperSet s) (htUpper : IsUpperSet t)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ((law (boxGraph c r) q ξ).map f).toMeasure.real s *
      ((law (boxGraph c r) q ξ).map f).toMeasure.real t ≤
      ((law (boxGraph c r) q ξ).map f).toMeasure.real (s ∩ t) := by
  simp only [Measure.real_def, PMF.toMeasure_map_apply _ _ _ measurable_from_top hs,
    PMF.toMeasure_map_apply _ _ _ measurable_from_top ht,
    PMF.toMeasure_map_apply _ _ _ measurable_from_top (hs.inter ht)]
  exact measure_positive_association q ξ _ _ (hsUpper.preimage hf) (htUpper.preimage hf)

/-- Pass a finite positive-association inequality to the weak limit on clopen events. -/
theorem clopen_positive_association_of_tendsto
    {μ : ℕ → ProbabilityMeasure LatticeConfiguration} {φ : ProbabilityMeasure LatticeConfiguration}
    (hφ : Tendsto μ atTop (𝓝 φ)) {s t : Set LatticeConfiguration}
    (hs : IsClopen s) (ht : IsClopen t)
    (hfinite : ∀ n, (μ n).toMeasure.real s * (μ n).toMeasure.real t ≤
      (μ n).toMeasure.real (s ∩ t)) :
    φ.toMeasure.real s * φ.toMeasure.real t ≤ φ.toMeasure.real (s ∩ t) := by
  have conv {A : Set LatticeConfiguration} (hA : IsClopen A) :
      Tendsto (fun n => (μ n A : ℝ)) atTop (𝓝 (φ A : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hφ hA)
  simpa using
      le_of_tendsto_of_tendsto' ((conv hs).mul (conv ht)) (conv (hs.inter ht))
        (by assumption)

/-- Positive association under the unique free-box law for any two increasing clopen events of the original lattice configuration space. -/
theorem freeBoxLimit_clopen_positive_association (q : Parameters)
    (s t : Set LatticeConfiguration) (hsClopen : IsClopen s)
    (htClopen : IsClopen t) (hsUpper : IsUpperSet s) (htUpper : IsUpperSet t) :
    (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q) s : ℝ) *
      (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q) t : ℝ) ≤
        (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q) (s ∩ t) : ℝ) := by
  let μ :=
    Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)
  have hweak :=
    (Classical.choose_spec (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)).1
      (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
  simpa using
      clopen_positive_association_of_tendsto hweak hsClopen htClopen (fun n =>
        boxMap_positive_association q (0, 0) n (BoundaryCondition.free ∅) _
          (fun _ _ => boxConfiguration_mono (0, 0) n)
          hsUpper htUpper hsClopen.isOpen.measurableSet htClopen.isOpen.measurableSet)

end
end PottsDiscontinuity.FK.Internal
