/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
The all-open comparison is antitone for wired laws with open exterior extension. -/
module
public import Mathlib

public import PottsDiscontinuity.FK.WiredBoxComparison
public import PottsDiscontinuity.FK.AntitoneCylinderConvergence
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
    ∃! μ : ProbabilityMeasure LatticeConfiguration,
      ∀ (c : ℕ → LatticeVertex) (r : ℕ → ℕ),
        (∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1))) →
        (∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n)) →
        Tendsto (fun n => wiredBoxProbabilityMeasure θ (c n) (r n)) atTop (𝓝 μ) := by
  
  
  obtain ⟨μ, hμ, _⟩ := probabilityMeasures_tendsto_of_antitone_allOpen  fun F m n hmn => wiredAllOpen_antitone_nnreal θ (0, 0) (0, 0) m n
                                                                    (latticeBox_mono (0, 0) hmn) F 
  
  refine ⟨μ,  by
                intro c r hnest hexhaust
                
                obtain ⟨ν, hν, _⟩ := probabilityMeasures_tendsto_of_antitone_allOpen (by
                                                                                        intro F m n hmn
                                                                                        exact wiredAllOpen_antitone_nnreal θ (c m) (c n) (r m) (r n)
                                                                                          (latticeBox_subset_of_nested hnest hmn) F)
                have hμF (F : Finset squareLattice.edgeSet)  :=
                  LatticeConfiguration.tendsto_allOpen_of_weak hμ F
                have hνF (F : Finset squareLattice.edgeSet)  :=
                  LatticeConfiguration.tendsto_allOpen_of_weak hν F
                have hμleν (F : Finset squareLattice.edgeSet) :
                    μ (LatticeConfiguration.allOpen F) ≤ ν (LatticeConfiguration.allOpen F) := le_of_tendsto_of_tendsto tendsto_const_nhds (hνF F)
                                                                                                 (Eventually.of_forall fun j =>
                                                                                                   Exists.casesOn
                                                                                                     (latticeBox_subset_eventually_of_nested_exhaustive origin_latticeBox_nested origin_latticeBox_exhaustive (c j)
                                                                                                       (r j))
                                                                                                     fun N hN =>
                                                                                                     le_of_tendsto_of_tendsto (hμF F) tendsto_const_nhds
                                                                                                       (eventually_atTop.mpr
                                                                                                         (Exists.intro N fun n hn => wiredAllOpen_antitone_nnreal θ (c j) (0, 0) (r j) n (hN n hn) F)))
                have hνleμ (F : Finset squareLattice.edgeSet) :
                    ν (LatticeConfiguration.allOpen F) ≤ μ (LatticeConfiguration.allOpen F) := le_of_tendsto_of_tendsto tendsto_const_nhds (hμF F)
                                                                                                 (Eventually.of_forall fun j =>
                                                                                                   Exists.casesOn (latticeBox_subset_eventually_of_nested_exhaustive hnest hexhaust (0, 0) j) fun N hN =>
                                                                                                     le_of_tendsto_of_tendsto (hνF F) tendsto_const_nhds
                                                                                                       (eventually_atTop.mpr
                                                                                                         (Exists.intro N fun n hn => wiredAllOpen_antitone_nnreal θ (0, 0) (c n) j (r n) (hN n hn) F)))
                have hμν : μ = ν := by
                  apply LatticeConfiguration.probabilityMeasure_eq_of_allOpen
                  all_goals grind
                rw [hμν]
                exact hν , ?_⟩
  intro ν hν
  
  exact tendsto_nhds_unique (hν (fun _ => (0, 0)) (fun n => n)
                               origin_latticeBox_nested origin_latticeBox_exhaustive) hμ

/-- In particular, the canonical wired boxes converge weakly to a probability measure. -/
theorem wiredBoxProbabilityMeasure_exists_limit (θ : Parameters) :
    ∃ μ : ProbabilityMeasure LatticeConfiguration,
      Tendsto  (wiredBoxProbabilityMeasure θ (0, 0))  atTop (𝓝 μ) := by
  obtain ⟨μ, hμ, _⟩ := wiredBoxLimit_existsUnique θ
  exact ⟨μ, hμ (fun _ => (0, 0)) (fun n => n)
    origin_latticeBox_nested origin_latticeBox_exhaustive⟩

end
end PottsDiscontinuity.FK
