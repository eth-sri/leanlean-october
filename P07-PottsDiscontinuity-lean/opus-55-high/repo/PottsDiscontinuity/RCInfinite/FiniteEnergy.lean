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
variable (i : Fin 2) (c : LatticeVertex) (r : ℕ)
def boxExtension (C : Configuration (boxGraph c r)) : LatticeConfiguration :=
  if i = 0 then boxConfiguration c r C else wiredBoxConfiguration c r C

def boxBoundary  : BoundaryCondition (BoxVertex c r) :=
  if i = 0 then BoundaryCondition.free ∅ else BoundaryCondition.wired (boxVertexBoundary c r)

@[simp] theorem boxExtension_at (C : Configuration (boxGraph c r)) (e : (boxGraph c r).edgeSet) :
    boxExtension i c r C (boxEdgeEmbedding c r e) = decide (e ∈ C) := by
  fin_cases i <;> simp [boxExtension]
end

theorem boxMeasure_apply (θ : Parameters) (i : Fin 2) (c : LatticeVertex) (r : ℕ)
    {A : Set LatticeConfiguration} (hA : MeasurableSet A) :
    (boxMeasure θ i c r : Measure LatticeConfiguration) A =
      measure (boxGraph c r) θ (boxBoundary i c r) ((boxExtension i c r) ⁻¹' A) := by
  unfold boxMeasure boxBoundary boxExtension
  split_ifs <;> exact PMF.toMeasure_map_apply _ _ _ measurable_from_top hA

theorem eventually_edge_in_box (e : Edge) :
    ∀ᶠ n : ℕ in atTop, ∃ f : (boxGraph (0, 0) n).edgeSet,
      boxEdgeEmbedding (0, 0) n f = e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    filter_upwards [eventually_mem_box x, eventually_mem_box y] with n hx hy
    exact ⟨⟨s(⟨x, (by rwa [latticeBox_origin_eq_box])⟩, ⟨y, (by rwa [latticeBox_origin_eq_box])⟩), he⟩, rfl⟩

end
end PottsDiscontinuity.RCInfinite
