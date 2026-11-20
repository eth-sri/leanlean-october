module

public import PottsDiscontinuity.FK.BoxLimits
public import PottsDiscontinuity.RCInfinite.SpatialComparison

/-! Whole-lattice extensions and cylinders for the literal ghost law. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace

section

variable
  (V : Finset (ℤ × ℤ))
    (C : FK.Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))

/-- Open exterior extension, retaining all sampled internal bonds. -/
def openExtension : FK.LatticeConfiguration :=
  fun e => decide (∀ f, FK.frozenEdgeEmbedding V f = e → f ∈ C)

@[simp] theorem openExtension_at
    (f : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet) :
    openExtension V C (FK.frozenEdgeEmbedding V f) = decide (f ∈ C) := by
  have h : (∀ g, FK.frozenEdgeEmbedding V g = FK.frozenEdgeEmbedding V f → g ∈ C) ↔ f ∈ C := by
    simp
  simp [openExtension]

end

/-- The same extension applied to the ordinary wired box law. -/
def openBoxProbabilityMeasure (θ : FK.Parameters) (n : ℕ) : ProbabilityMeasure FK.LatticeConfiguration :=
  FK.frozenExtendedProbabilityMeasure θ (box n) 1 (openExtension (box n))

theorem openBoxProbabilityMeasure_eq_wired (θ : FK.Parameters) (n : ℕ) :
    openBoxProbabilityMeasure θ n = FK.wiredBoxProbabilityMeasure θ (0, 0) n := by
  unfold openBoxProbabilityMeasure
  have key : ∀ (c : FK.LatticeVertex) (r : ℕ) (S : Finset (ℤ × ℤ)), FK.latticeBox c r = S →
      FK.frozenExtendedProbabilityMeasure θ S 1 (openExtension S) =
        FK.wiredBoxProbabilityMeasure θ c r := by
    rintro c r S rfl
    have hext : openExtension (FK.latticeBox c r) = FK.wiredBoxConfiguration c r := by
      funext C e
      unfold openExtension FK.wiredBoxConfiguration
      exact decide_eq_decide.mpr Iff.rfl
    rw [hext]
    rfl
  exact key (0, 0) n _ (FK.latticeBox_origin_eq_box n)

def openBoxCylinderEvent (n : ℕ) (F : Finset squareLattice.edgeSet) :
    Set (FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :=
  {C | ∀ e ∈ F, ∀ f, FK.frozenEdgeEmbedding (box n) f = e → f ∈ C}

theorem openBoxCylinderEvent_upper (n : ℕ) (F : Finset squareLattice.edgeSet) :
    IsUpperSet (openBoxCylinderEvent n F) := by
  intro C D hCD hC e he f hf
  exact hCD (hC e he f hf)

theorem openExtension_mem_allOpen (n : ℕ)
    (C : FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))))
    (F : Finset squareLattice.edgeSet) :
    openExtension (box n) C ∈ FK.LatticeConfiguration.allOpen F ↔ C ∈ openBoxCylinderEvent n F := by
  simp only [openExtension, FK.LatticeConfiguration.allOpen, openBoxCylinderEvent,
    Set.mem_ofPred_eq, decide_eq_true_eq]

theorem boxEdges_origin_eq_range (n : ℕ) :
    RCInfinite.boxEdges (0, 0) n = Set.range (FK.frozenEdgeEmbedding (box n)) := by
  suffices ∀ S, FK.latticeBox (0, 0) n = S → RCInfinite.boxEdges (0, 0) n = Set.range (FK.frozenEdgeEmbedding S) from
    this _ (FK.latticeBox_origin_eq_box n)
  aesop

end
end PottsDiscontinuity.Potts
