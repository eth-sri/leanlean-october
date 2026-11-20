/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
The all-open comparison is antitone for wired laws with open exterior extension. -/
module

public import PottsDiscontinuity.FK.WiredBoxComparison
public import PottsDiscontinuity.FK.CylinderConvergence
public import PottsDiscontinuity.FK.BoxExhaustion

/-! A common weak limit of wired FK laws along every nested exhaustive box sequence. -/

@[expose] public section

namespace PottsDiscontinuity.FK

open MeasureTheory Filter Topology
noncomputable section

private theorem wiredAllOpen_antitone_nnreal (θ : Parameters)
    (c d : LatticeVertex) (r s : ℕ)
    (hbox : latticeBox c r ⊆ latticeBox d s) (F : Finset squareLattice.edgeSet) :
    wiredBoxProbabilityMeasure θ d s (LatticeConfiguration.allOpen F) ≤
      wiredBoxProbabilityMeasure θ c r (LatticeConfiguration.allOpen F) := by
  have h := wiredBoxProbabilityMeasure_allOpen_antitone θ c d r s hbox F
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
  exact ENNReal.coe_le_coe.mp h

/-- The wired finite-volume laws have a unique common weak limit along every
nested exhaustive sequence of translated square boxes. -/
theorem wiredBoxLimit_existsUnique (θ : Parameters) :
    ∃! μ, WeakBoxLimit (wiredBoxProbabilityMeasure θ) μ := by
  refine boxLimit_existsUnique_of_compare (Y := Finset squareLattice.edgeSet → NNRealᵒᵈ)
    (wiredBoxProbabilityMeasure θ) cylinderProbabilityCoordinates continuous_cylinderProbabilityCoordinates
    (fun _ _ e => LatticeConfiguration.probabilityMeasure_eq_of_allOpen fun F => congrFun e F) ?_ ?_
  · intro a b r s h F
    exact wiredAllOpen_antitone_nnreal θ a b r s h F
  · intro c r hn
    exact (probabilityMeasures_tendsto_of_antitone_allOpen fun F m n hmn =>
      wiredAllOpen_antitone_nnreal θ (c m) (c n) (r m) (r n) (latticeBox_subset_of_nested hn hmn) F).exists

/-- In particular, the canonical wired boxes converge weakly to a probability measure. -/
theorem wiredBoxProbabilityMeasure_exists_limit (θ : Parameters) :
    ∃ μ : ProbabilityMeasure LatticeConfiguration,
      Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ) := by
  obtain ⟨μ, hμ, _⟩ := wiredBoxLimit_existsUnique θ
  exact ⟨μ, hμ.atOrigin⟩

end
end PottsDiscontinuity.FK
