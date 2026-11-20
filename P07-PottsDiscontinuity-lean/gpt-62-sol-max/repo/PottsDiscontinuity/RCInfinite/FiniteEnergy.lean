module

public import PottsDiscontinuity.RCInfinite.Cylinders
public import PottsDiscontinuity.FK.FiniteEnergy

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section

attribute [local instance] configurationMeasurableSpace
local instance edgeDecidableEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet :=
  Classical.decEq _

def boxExtension (i : Fin 2) (c : LatticeVertex) (r : ℕ)
    (C : Configuration (boxGraph c r)) : LatticeConfiguration :=
  if i = 0 then boxConfiguration c r C else wiredBoxConfiguration c r C

def boxBoundary (i : Fin 2) (c : LatticeVertex) (r : ℕ) : BoundaryCondition (BoxVertex c r) :=
  if i = 0 then BoundaryCondition.free ∅ else BoundaryCondition.wired (boxVertexBoundary c r)

@[simp] theorem boxExtension_at (i : Fin 2) (c : LatticeVertex) (r : ℕ)
    (C : Configuration (boxGraph c r)) (e : (boxGraph c r).edgeSet) :
    boxExtension i c r C (boxEdgeEmbedding c r e) = decide (e ∈ C) := by
  classical
  fin_cases i <;> simp [boxExtension]

theorem boxMeasure_apply (θ : Parameters) (i : Fin 2) (c : LatticeVertex) (r : ℕ)
    {A : Set LatticeConfiguration} (hA : MeasurableSet A) :
    (boxMeasure θ i c r : Measure LatticeConfiguration) A =
      measure (boxGraph c r) θ (boxBoundary i c r) ((boxExtension i c r) ⁻¹' A) := by
  classical
  unfold boxMeasure boxBoundary boxExtension
  split_ifs
  · exact PMF.toMeasure_map_apply _ _ _ measurable_from_top hA
  · exact PMF.toMeasure_map_apply _ _ _ measurable_from_top hA

theorem eventually_edge_in_box (e : Edge) :
    ∀ᶠ n : ℕ in atTop, ∃ f : (boxGraph (0, 0) n).edgeSet,
      boxEdgeEmbedding (0, 0) n f = e := by
  filter_upwards [eventually_edge_lift_box e] with n hn
  rw [← latticeBox_origin_eq_box] at hn
  exact hn.imp fun f hf => Subtype.ext hf

end
end PottsDiscontinuity.RCInfinite
