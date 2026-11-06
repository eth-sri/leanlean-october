/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module
public import Mathlib

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
    ∃! μ : ProbabilityMeasure LatticeConfiguration,
      ∀ (c : ℕ → LatticeVertex) (r : ℕ → ℕ),
        (∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1))) →
        (∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n)) →
        Tendsto (fun n => boxProbabilityMeasure q (c n) (r n)) atTop (𝓝 μ) := by
  
  
  obtain ⟨μ, hμ, hμunique⟩ := probabilityMeasures_tendsto_of_monotone_allOpen  fun F ⦃m n⦄ hmn => allOpen_mono_nnreal q (0, 0) (0, 0) m n (latticeBox_mono (0, 0) hmn) F 
  
  refine ⟨μ,  by
                intro c r hnest hexhaust
                
                obtain ⟨ν, hν, hνunique⟩ :=
                  probabilityMeasures_tendsto_of_monotone_allOpen (by
                                                                     intro F m n hmn
                                                                     simpa using allOpen_mono_nnreal q (c m) (c n) (r m) (r n)
                                                                       (latticeBox_subset_of_nested hnest hmn) F)
                have hμF (F : Finset squareLattice.edgeSet)  :=
                  LatticeConfiguration.tendsto_allOpen_of_weak hμ F
                have hνF (F : Finset squareLattice.edgeSet)  :=
                  LatticeConfiguration.tendsto_allOpen_of_weak hν F
                have hνleμ (F : Finset squareLattice.edgeSet) :
                    ν (LatticeConfiguration.allOpen F) ≤ μ (LatticeConfiguration.allOpen F) := le_of_tendsto' (hνF F) fun j =>
                                                                                                 Exists.casesOn
                                                                                                   (latticeBox_subset_eventually_of_nested_exhaustive origin_latticeBox_nested origin_latticeBox_exhaustive (c j)
                                                                                                     (r j))
                                                                                                   fun N hN =>
                                                                                                   le_of_tendsto_of_tendsto tendsto_const_nhds (hμF F)
                                                                                                     (eventually_atTop.mpr (Exists.intro N fun n hn => allOpen_mono_nnreal q (c j) (0, 0) (r j) n (hN n hn) F))
                have hμleν (F : Finset squareLattice.edgeSet) :
                    μ (LatticeConfiguration.allOpen F) ≤ ν (LatticeConfiguration.allOpen F) := le_of_tendsto' (hμF F) fun j =>
                                                                                                 Exists.casesOn (latticeBox_subset_eventually_of_nested_exhaustive hnest hexhaust (0, 0) j) fun N hN =>
                                                                                                   le_of_tendsto_of_tendsto tendsto_const_nhds (hνF F)
                                                                                                     (eventually_atTop.mpr (Exists.intro N fun n hn => allOpen_mono_nnreal q (0, 0) (c n) j (r n) (hN n hn) F))
                have hμν : μ = ν := by
                  apply LatticeConfiguration.probabilityMeasure_eq_of_allOpen
                  all_goals grind
                rw [hμν]
                exact hν , ?_⟩
  intro ν hν
  
  exact tendsto_nhds_unique (hν (fun _ => (0, 0)) (fun n => n)
                               origin_latticeBox_nested origin_latticeBox_exhaustive) hμ

end
end PottsDiscontinuity.FK.Internal
