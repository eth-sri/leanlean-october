/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.BoxComparison
public import PottsDiscontinuity.FK.CylinderConvergence
public import PottsDiscontinuity.FK.BoxExhaustion

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK.Internal

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
theorem freeBoxLimit_existsUnique {q : Parameters} :
    ∃! μ, IsBoxLimit (boxProbabilityMeasure q) μ := by
  apply existsUnique_boxLimit
  intro F
  exact exists_boxLimit_of_mono _ 1 (fun a n => (boxProbabilityMeasure q a n).apply_le_one _)
    (fun c d r s h => allOpen_mono_nnreal q c d r s h F)

end
end PottsDiscontinuity.FK.Internal
