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

variable (θ : Parameters)

private theorem wiredAllOpen_antitone_nnreal
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
theorem wiredBoxLimit_existsUnique :
    ∃! μ, IsBoxLimit (wiredBoxProbabilityMeasure θ) μ := by
  apply existsUnique_boxLimit
  intro F
  exact exists_boxLimit_of_mono (X := NNRealᵒᵈ) _ 0 (fun c n => (wiredBoxProbabilityMeasure θ c n (LatticeConfiguration.allOpen F)).property)
    (fun c d r s h => wiredAllOpen_antitone_nnreal θ c d r s h F)

/-- In particular, the canonical wired boxes converge weakly to a probability measure. -/
theorem wiredBoxProbabilityMeasure_exists_limit :
    ∃ μ : ProbabilityMeasure LatticeConfiguration,
      Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ) := by
  obtain ⟨μ, hμ, _⟩ := wiredBoxLimit_existsUnique θ
  exact ⟨μ, hμ (fun _ => (0, 0)) (fun n => n)
    origin_latticeBox_nested origin_latticeBox_exhaustive⟩

end
end PottsDiscontinuity.FK
