/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.CylinderDetermination
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Weak convergence from monotone finite cylinders

On the compact whole-lattice configuration space, monotonicity of every finite
all-open cylinder probability forces weak convergence of the probability laws.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open Set MeasureTheory Filter Topology
noncomputable section


/-- The coordinate map recording every finite all-open cylinder probability. -/
def cylinderProbabilityCoordinates (μ : ProbabilityMeasure LatticeConfiguration) :
    Finset squareLattice.edgeSet → NNReal :=
  fun F => μ (LatticeConfiguration.allOpen F)

theorem continuous_cylinderProbabilityCoordinates :
    Continuous cylinderProbabilityCoordinates := by
  refine continuous_pi fun F => ?_
  rw [continuous_iff_continuousAt]
  intro μ
  exact LatticeConfiguration.tendsto_allOpen_of_weak tendsto_id F

/-- Coordinatewise convergence on all-open cylinders implies weak convergence. -/
private theorem probabilityMeasures_tendsto_of_allOpen
    {μs : ℕ → ProbabilityMeasure LatticeConfiguration}
    (h : ∀ F : Finset squareLattice.edgeSet, ∃ a,
      Tendsto (fun n => μs n (LatticeConfiguration.allOpen F)) atTop (𝓝 a)) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration, Tendsto μs atTop (𝓝 μ) := by
  obtain ⟨μ, φ, hφ, hweak⟩ := CompactSpace.tendsto_subseq μs
  let κ := cylinderProbabilityCoordinates
  have hinj : Function.Injective κ := fun _ _ e =>
    LatticeConfiguration.probabilityMeasure_eq_of_allOpen fun F => congrFun e F
  have hclosed := continuous_cylinderProbabilityCoordinates.isClosedEmbedding hinj
  have hκ : Tendsto (κ ∘ μs) atTop (𝓝 (κ μ)) := by
    apply tendsto_pi_nhds.2
    intro F
    obtain ⟨a, ha⟩ := h F
    have he := tendsto_nhds_unique
      (LatticeConfiguration.tendsto_allOpen_of_weak hweak F) (ha.comp hφ.tendsto_atTop)
    simpa [κ, cylinderProbabilityCoordinates, he] using ha
  have hfull := hclosed.tendsto_nhds_iff.mpr hκ
  exact ⟨μ, hfull, fun _ hν => tendsto_nhds_unique hν hfull⟩

/-- If every finite all-open cylinder probability is monotone along a sequence,
then the sequence converges weakly to a unique probability measure. -/
theorem probabilityMeasures_tendsto_of_monotone_allOpen
    {μs : ℕ → ProbabilityMeasure LatticeConfiguration}
    (hmono : ∀ F : Finset squareLattice.edgeSet,
      Monotone (fun n => μs n (LatticeConfiguration.allOpen F))) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration, Tendsto μs atTop (𝓝 μ) := by
  refine probabilityMeasures_tendsto_of_allOpen fun F => ⟨_, tendsto_atTop_ciSup (hmono F) ⟨1, ?_⟩⟩
  rintro _ ⟨n, rfl⟩
  simp

/-- Antitone all-open cylinder coordinates also give weak convergence. -/
theorem probabilityMeasures_tendsto_of_antitone_allOpen
    {μs : ℕ → ProbabilityMeasure LatticeConfiguration}
    (hanti : ∀ F : Finset squareLattice.edgeSet,
      Antitone (fun n => μs n (LatticeConfiguration.allOpen F))) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration, Tendsto μs atTop (𝓝 μ) :=
  probabilityMeasures_tendsto_of_allOpen fun F =>
    ⟨_, tendsto_atTop_ciInf (hanti F) ⟨0, fun _ _ => zero_le⟩⟩

end
end PottsDiscontinuity.FK
