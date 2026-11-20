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

section
variable (θ : Parameters) (i : Fin 2) (c : LatticeVertex) (r : ℕ)
    (C : Configuration (boxGraph c r))
include i

include C in
def boxExtension : LatticeConfiguration :=
  if i = 0 then boxConfiguration c r C else wiredBoxConfiguration c r C

def boxBoundary : BoundaryCondition (BoxVertex c r) :=
  if i = 0 then BoundaryCondition.free ∅ else BoundaryCondition.wired (boxVertexBoundary c r)

@[simp] theorem boxExtension_at (e : (boxGraph c r).edgeSet) :
    boxExtension i c r C (boxEdgeEmbedding c r e) = decide (e ∈ C) := by
  classical
  fin_cases i <;> simp [boxExtension]

theorem boxMeasure_apply
    {A : Set LatticeConfiguration} (hA : MeasurableSet A) :
    (boxMeasure θ i c r : Measure LatticeConfiguration) A =
      measure (boxGraph c r) θ (boxBoundary i c r) ((boxExtension i c r) ⁻¹' A) := by
  classical
  unfold boxMeasure boxBoundary boxExtension
  split_ifs
  · exact PMF.toMeasure_map_apply _ _ _ measurable_from_top hA
  · exact PMF.toMeasure_map_apply _ _ _ measurable_from_top hA

end

theorem eventually_edge_in_box (e : Edge) :
    ∀ᶠ n : ℕ in atTop, ∃ f : (boxGraph (0, 0) n).edgeSet,
      boxEdgeEmbedding (0, 0) n f = e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    filter_upwards [eventually_mem_box x, eventually_mem_box y] with n hx hy
    have hx' : x ∈ latticeBox (0, 0) n := by rwa [latticeBox_origin_eq_box]
    have hy' : y ∈ latticeBox (0, 0) n := by rwa [latticeBox_origin_eq_box]
    exact ⟨⟨s(⟨x, hx'⟩, ⟨y, hy'⟩), he⟩, rfl⟩

end
end PottsDiscontinuity.RCInfinite
