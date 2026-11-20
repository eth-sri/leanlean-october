/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.BoxComparison
public import PottsDiscontinuity.FK.CylinderConvergence
public import PottsDiscontinuity.FK.BoxExhaustion

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK

noncomputable section


private theorem allOpen_mono_nnreal (q : Parameters) (a b : LatticeVertex)
    (r s : ℕ) (hab : latticeBox a r ⊆ latticeBox b s)
    (F : Finset squareLattice.edgeSet) :
    boxProbabilityMeasure q a r (LatticeConfiguration.allOpen F) ≤
      boxProbabilityMeasure q b s (LatticeConfiguration.allOpen F) := by
  have h := boxProbabilityMeasure_allOpen_mono q a b r s hab F
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
  exact ENNReal.coe_le_coe.mp h

/-- The exact common weak limit of the original finite free FK laws along every
nested exhaustive sequence of lattice boxes. -/
theorem freeBoxLimit_existsUnique (q : Parameters) :
    ∃! μ, WeakBoxLimit (boxProbabilityMeasure q) μ := by
  refine boxLimit_existsUnique_of_compare
    (boxProbabilityMeasure q) cylinderProbabilityCoordinates continuous_cylinderProbabilityCoordinates
    (fun _ _ e => LatticeConfiguration.probabilityMeasure_eq_of_allOpen fun F => congrFun e F) ?_ ?_
  · intro a b r s h F
    exact allOpen_mono_nnreal q a b r s h F
  · intro c r hn
    exact (probabilityMeasures_tendsto_of_monotone_allOpen fun F m n hmn =>
      allOpen_mono_nnreal q (c m) (c n) (r m) (r n) (latticeBox_subset_of_nested hn hmn) F).exists

end
end PottsDiscontinuity.FK
