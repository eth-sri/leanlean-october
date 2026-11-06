/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.LatticeEmbedding
public import Mathlib.Topology.Path
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsDiscontinuity.FK.Curves



noncomputable section

/-- Straight-segment interpolation of an actual nearest-neighbor lattice walk.
The recursive concatenation retains the walk order and all repeated visits. -/
def latticeWalkPath (δ : PositiveMesh) : {u v : LatticeVertex} →
    squareLattice.Walk u v → Path (latticeEmbed δ u) (latticeEmbed δ v)
  | _, _, .nil => Path.refl _
  | u, _, .cons (v := v) _h p =>
      (Path.segment (latticeEmbed δ u) (latticeEmbed δ v)).trans
        (latticeWalkPath δ p)

/-- Every point of the interpolated path belongs to a segment joining two
vertices visited by the original walk. -/
theorem latticeWalkPath_range_subset_segments (δ : PositiveMesh)
    {u v : LatticeVertex} (p : squareLattice.Walk u v) :
    Set.range (latticeWalkPath δ p) ⊆
      {z | ∃ x y : LatticeVertex, x ∈ p.support ∧ y ∈ p.support ∧
        (x = y ∨ squareLattice.Adj x y) ∧
        z ∈ Set.range (Path.segment (latticeEmbed δ x) (latticeEmbed δ y))} := by
  induction p with
  | @nil u0 =>
      
      aesop
  | @cons u v w h p ih =>
      intro z hz
      change z ∈ Set.range
        ((Path.segment (latticeEmbed δ u) (latticeEmbed δ v)).trans
          (latticeWalkPath δ p)) at hz
      rw [Path.trans_range] at hz
      rcases hz with hfirst | htail
      · aesop
      · obtain ⟨x, y, hx, hy, hxy, hseg⟩ := ih htail
        exact ⟨x, y, by simp [hx], by simp [hy], hxy, hseg⟩

end
end PottsDiscontinuity.FK.Curves
