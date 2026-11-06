/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
The monotone cylinder argument is adapted to antitone cylinder probabilities. -/
module
public import Mathlib

public import PottsDiscontinuity.FK.CylinderConvergence

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK

noncomputable section

/-- If every finite all-open cylinder probability is antitone along a sequence,
then the sequence converges weakly to a unique probability measure. -/
theorem probabilityMeasures_tendsto_of_antitone_allOpen
    {μs : ℕ → ProbabilityMeasure LatticeConfiguration}
    (hanti : ∀ F : Finset squareLattice.edgeSet,
      Antitone  fun n => μs n (LatticeConfiguration.allOpen F) ) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration, Tendsto μs atTop (𝓝 μ) := by
  obtain ⟨μ, φ, hφ, hweak⟩ := CompactSpace.tendsto_subseq μs
  
  
  
  
  
  
  have hfull  := ((continuous_cylinderProbabilityCoordinates).isClosedEmbedding  fun ⦃μ₁ μ₂⦄ h => LatticeConfiguration.probabilityMeasure_eq_of_allOpen (congrFun h) ).tendsto_nhds_iff.mpr (tendsto_pi_nhds.mpr fun F =>
                                                                                                                                                                                               let f := fun n => (μs n) (LatticeConfiguration.allOpen F);
                                                                                                                                                                                               Eq.mpr (congrArg (fun _a => Tendsto f atTop (𝓝 _a)) ((fun (F : Finset squareLattice.edgeSet) => let f := fun n => (μs n) (LatticeConfiguration.allOpen F);
                                                                                                                                                                                                                                                                                                         tendsto_nhds_unique (LatticeConfiguration.tendsto_allOpen_of_weak hweak F)
                                                                                                                                                                                                                                                                                                           (Tendsto.comp (tendsto_atTop_ciInf (hanti F) (Exists.intro 0 fun x x_1 => zero_le)) (StrictMono.tendsto_atTop hφ))) F))
                                                                                                                                                                                                 (tendsto_atTop_ciInf (hanti F) (Exists.intro 0 fun x x_1 => zero_le)))
  refine ⟨μ, hfull, ?_⟩
  intro ν hν
  exact tendsto_nhds_unique hν hfull

end
end PottsDiscontinuity.FK
