/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
The exterior extension is open and the finite boundary is wired. -/
module

public import PottsDiscontinuity.FK.BoxCylinders
public import PottsDiscontinuity.Frozen.Defs.VertexBoundary

/-! Wired finite-box FK laws on the common whole-lattice carrier. -/

@[expose] public section

namespace PottsDiscontinuity.FK

open MeasureTheory Filter Topology
noncomputable section

/-- The frozen vertex boundary, on the vertex carrier of a translated box. -/
def boxVertexBoundary (c : LatticeVertex) (r : ℕ) : Set (BoxVertex c r) :=
  {x | x.val ∈ vertexBoundary (latticeBox c r)}

section
variable (c : LatticeVertex) (r : ℕ) (A : Configuration (boxGraph c r))
/-- Extend an actual box configuration by open edges outside the box. -/
def wiredBoxConfiguration  : LatticeConfiguration := by
  classical
  exact fun e => decide (∀ f, boxEdgeEmbedding c r f = e → f ∈ A)

theorem wiredBoxConfiguration_open_iff (e : squareLattice.edgeSet) :
    wiredBoxConfiguration c r A e = true ↔
      ∀ f, boxEdgeEmbedding c r f = e → f ∈ A := by
  grind [wiredBoxConfiguration]

/-- Open extension preserves every edge state sampled in the finite graph. -/
@[simp] theorem wiredBoxConfiguration_at (e : (boxGraph c r).edgeSet) :
    wiredBoxConfiguration c r A (boxEdgeEmbedding c r e) = decide (e ∈ A) := by
  have h : (∀ f, boxEdgeEmbedding c r f = boxEdgeEmbedding c r e → f ∈ A) ↔ e ∈ A := by
    constructor
    · exact fun h => h e rfl
    · intro he f hf
      exact (boxEdgeEmbedding c r).injective hf ▸ he
  simp only [wiredBoxConfiguration, h]

theorem wiredBoxConfiguration_outside (e : squareLattice.edgeSet)
    (he : e ∉ Set.range (boxEdgeEmbedding c r)) :
    wiredBoxConfiguration c r A e = true := by
  rw [wiredBoxConfiguration_open_iff]
  tauto
end

section
variable (θ : Parameters) (c : LatticeVertex) (r : ℕ)
/-- The exact finite wired law, followed by the open exterior extension. -/
def wiredBoxLaw  : PMF LatticeConfiguration :=
  (law (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))).map
    (wiredBoxConfiguration c r)

/-- The wired box law as a probability measure on the natural product space. -/
def wiredBoxProbabilityMeasure  :
    ProbabilityMeasure LatticeConfiguration :=
  ⟨(wiredBoxLaw θ c r).toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩
end

section
variable (c : LatticeVertex) (r : ℕ)
/-- The finite event seen by an all-open cylinder under open extension. -/
def wiredBoxCylinderEvent (F : Finset squareLattice.edgeSet) : Set (Configuration (boxGraph c r)) :=
  {A | ∀ e ∈ F, ∀ f, boxEdgeEmbedding c r f = e → f ∈ A}

theorem wiredBoxCylinderEvent_upper (F : Finset squareLattice.edgeSet) : IsUpperSet (wiredBoxCylinderEvent c r F) := by
  tauto

theorem wiredBoxConfiguration_mem_allOpen (A : Configuration (boxGraph c r)) (F : Finset squareLattice.edgeSet) :
    wiredBoxConfiguration c r A ∈ LatticeConfiguration.allOpen F ↔
      A ∈ wiredBoxCylinderEvent c r F := by
  simp only [LatticeConfiguration.allOpen, wiredBoxCylinderEvent, Set.mem_ofPred_eq,
    wiredBoxConfiguration_open_iff]
end

attribute [local instance] configurationMeasurableSpace

/-- A common-carrier all-open probability is exactly the finite wired event probability. -/
theorem wiredBoxProbabilityMeasure_allOpen (θ : Parameters) (c : LatticeVertex) (r : ℕ)
    (F : Finset squareLattice.edgeSet) :
    (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) =
      measure (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))
        (wiredBoxCylinderEvent c r F) := by
  change ((law (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))).map
    (wiredBoxConfiguration c r)).toMeasure _ = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  congr 1
  grind [wiredBoxConfiguration_mem_allOpen]

end
end PottsDiscontinuity.FK
