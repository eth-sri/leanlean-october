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

section
variable (θ : Parameters) (c : LatticeVertex) (r : ℕ) (A : Configuration (boxGraph c r))
    (F : Finset squareLattice.edgeSet) (e : squareLattice.edgeSet)

/-- The frozen vertex boundary, on the vertex carrier of a translated box. -/
def boxVertexBoundary : Set (BoxVertex c r) :=
  {x | x.val ∈ vertexBoundary (latticeBox c r)}

include A in
/-- Extend an actual box configuration by open edges outside the box. -/
def wiredBoxConfiguration : LatticeConfiguration := by
  classical
  exact fun e => decide (∀ f, boxEdgeEmbedding c r f = e → f ∈ A)

theorem wiredBoxConfiguration_open_iff :
    wiredBoxConfiguration c r A e = true ↔
      ∀ f, boxEdgeEmbedding c r f = e → f ∈ A := by
  classical
  simp only [wiredBoxConfiguration, decide_eq_true_eq]

/-- Open extension preserves every edge state sampled in the finite graph. -/
@[simp] theorem wiredBoxConfiguration_at {c : LatticeVertex} (r : ℕ)
    (A : Configuration (boxGraph c r)) (e : (boxGraph c r).edgeSet) :
    wiredBoxConfiguration c r A (boxEdgeEmbedding c r e) = decide (e ∈ A) := by
  classical
  have h : (∀ f, boxEdgeEmbedding c r f = boxEdgeEmbedding c r e → f ∈ A) ↔ e ∈ A := by
    constructor
    · exact fun h => h e rfl
    · intro he f hf
      exact (boxEdgeEmbedding c r).injective hf ▸ he
  simp only [wiredBoxConfiguration, h]

theorem wiredBoxConfiguration_outside
    (he : e ∉ Set.range (boxEdgeEmbedding c r)) :
    wiredBoxConfiguration c r A e = true := by
  rw [wiredBoxConfiguration_open_iff]
  intro f hf
  exact (he ⟨f, hf⟩).elim

include θ c r in
/-- The exact finite wired law, followed by the open exterior extension. -/
def wiredBoxLaw : PMF LatticeConfiguration :=
  (law (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))).map
    (wiredBoxConfiguration c r)

include θ c r in
/-- The wired box law as a probability measure on the natural product space. -/
def wiredBoxProbabilityMeasure :
    ProbabilityMeasure LatticeConfiguration :=
  ⟨(wiredBoxLaw θ c r).toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩

include F in
/-- The finite event seen by an all-open cylinder under open extension. -/
def wiredBoxCylinderEvent : Set (Configuration (boxGraph c r)) :=
  {A | ∀ e ∈ F, ∀ f, boxEdgeEmbedding c r f = e → f ∈ A}

theorem wiredBoxCylinderEvent_upper : IsUpperSet (wiredBoxCylinderEvent c r F) := by
  intro A B hAB hA e he f hf
  exact hAB (hA e he f hf)

theorem wiredBoxConfiguration_mem_allOpen :
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
  ext A
  exact wiredBoxConfiguration_mem_allOpen c r A F

end
end PottsDiscontinuity.FK
