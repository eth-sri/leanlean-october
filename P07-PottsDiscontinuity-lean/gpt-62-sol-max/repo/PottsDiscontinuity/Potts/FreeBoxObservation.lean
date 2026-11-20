module

public import PottsDiscontinuity.Infra.ClopenProbability

public import PottsDiscontinuity.Potts.BoxObservation

/-! Free finite-volume observations and their infinite-volume domination. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace

section

variable
  (V : Finset (ℤ × ℤ))
    (C : FK.Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))

/-- Closed exterior extension of an actual free finite configuration. -/
def closedExtension : FK.LatticeConfiguration :=
  fun e => decide (∃ f, FK.frozenEdgeEmbedding V f = e ∧ f ∈ C)

@[simp] theorem closedExtension_at
    (f : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet) :
    closedExtension V C (FK.frozenEdgeEmbedding V f) = decide (f ∈ C) := by
  have h : (∃ g, FK.frozenEdgeEmbedding V g = FK.frozenEdgeEmbedding V f ∧ g ∈ C) ↔ f ∈ C := by
    constructor
    · rintro ⟨g, hg, hmem⟩
      simp_all
    tauto
  simp only [closedExtension, h]

end

def closedBoxProbabilityMeasure (θ : FK.Parameters) (n : ℕ) : ProbabilityMeasure FK.LatticeConfiguration :=
  FK.frozenExtendedProbabilityMeasure θ (box n) 0 (closedExtension (box n))

theorem closedBoxProbabilityMeasure_eq_free (θ : FK.Parameters) (n : ℕ) :
    closedBoxProbabilityMeasure θ n = FK.boxProbabilityMeasure θ (0, 0) n := by
  unfold closedBoxProbabilityMeasure
  rw [← FK.latticeBox_origin_eq_box n]
  have hext : closedExtension (FK.latticeBox (0, 0) n) = FK.boxConfiguration (0, 0) n := by
    funext C e
    unfold closedExtension FK.boxConfiguration
    apply Bool.decide_congr
    constructor
    · rintro ⟨f, hf, hmem⟩
      exact Finset.mem_map.mpr ⟨f, hmem, hf⟩
    · rintro h
      obtain ⟨f, hmem, hf⟩ := Finset.mem_map.mp h
      tauto
  rw [hext, FK.frozenExtendedProbabilityMeasure_free]

@[simp] theorem boxObservation_closedExtension_self (n : ℕ)
    (C : FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :
    boxObservation n (closedExtension (box n) C) = C :=
  observation_ext_eq _ (closedExtension (box n)) (closedExtension_at (box n)) C

end
end PottsDiscontinuity.Potts
