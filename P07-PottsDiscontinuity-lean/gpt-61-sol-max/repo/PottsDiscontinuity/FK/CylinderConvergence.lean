/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module
public import Mathlib

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

/-- If every finite all-open cylinder probability is monotone along a sequence,
then the sequence converges weakly to a unique probability measure. -/
theorem probabilityMeasures_tendsto_of_monotone_allOpen
    {μs : ℕ → ProbabilityMeasure LatticeConfiguration}
    (hmono : ∀ F : Finset squareLattice.edgeSet,
      Monotone  fun n => μs n (LatticeConfiguration.allOpen F) ) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration, Tendsto μs atTop (𝓝 μ) := by
  obtain ⟨μ, φ, hφ, hweak⟩ := CompactSpace.tendsto_subseq μs
  have hlimit (F : Finset squareLattice.edgeSet) :
      μ (LatticeConfiguration.allOpen F) =
        ⨆ n, μs n (LatticeConfiguration.allOpen F) := by
    
    
    
    have ht := tendsto_atTop_ciSup (hmono F) (by
                                         refine ⟨1, ?_⟩
                                         rintro x ⟨n, rfl⟩
                                         aesop)
    
    
    exact tendsto_nhds_unique (LatticeConfiguration.tendsto_allOpen_of_weak hweak F) (ht.comp hφ.tendsto_atTop)
  
  
  
  
  
  have hfull  := ((continuous_cylinderProbabilityCoordinates).isClosedEmbedding  fun ⦃μ₁ μ₂⦄ h => LatticeConfiguration.probabilityMeasure_eq_of_allOpen (congrFun h) ).tendsto_nhds_iff.mpr (by
                                                 apply tendsto_pi_nhds.2
                                                 intro F
                                                 
                                                 
                                                 
                                                 
                                                 change Tendsto (fun n => μs n (LatticeConfiguration.allOpen F)) atTop (𝓝 (μ (LatticeConfiguration.allOpen F)))
                                                 rw [hlimit F]
                                                 exact (tendsto_atTop_ciSup (hmono F) (by
                                                                                             refine ⟨1, ?_⟩
                                                                                             rintro x ⟨n, rfl⟩
                                                                                             all_goals aesop)))
  refine ⟨μ, hfull, ?_⟩
  intro ν hν
  exact tendsto_nhds_unique hν hfull

end
end PottsDiscontinuity.FK
