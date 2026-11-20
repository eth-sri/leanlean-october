/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Only bond states and actual primal graphs are retained. -/
module

public import PottsDiscontinuity.Duality.LatticePorts
public import PottsDiscontinuity.FK.BoxLaw
public import PottsDiscontinuity.Frozen.Defs.RCInfiniteOpenGraph

@[expose] public section

namespace PottsDiscontinuity.FK.Medial

/-- The square-lattice edge underlying a normalized actual lattice bond. -/
def latticeBondEdge (b : LatticeBond) : squareLattice.edgeSet :=
  ⟨b.toSym2, b.toSym2_mem_edgeSet⟩

/-- Read the actual original-edge state at a bond, without introducing a second
configuration carrier. -/
def latticeConfigurationBondState (ω : LatticeConfiguration) (b : LatticeBond) : Bool :=
  ω (latticeBondEdge b)

theorem rcInfiniteOpenGraph_adj_iff (ω : LatticeConfiguration) (u v : LatticeVertex) :
    (rcInfiniteOpenGraph ω).Adj u v ↔ ∃ h : squareLattice.Adj u v,
      ω ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true := by
  rw [rcInfiniteOpenGraph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨fun ⟨⟨h, hω⟩, _⟩ => ⟨squareLattice.mem_edgeSet.mp h, hω⟩,
    fun ⟨h, hω⟩ => ⟨⟨squareLattice.mem_edgeSet.mpr h, hω⟩, h.ne⟩⟩

theorem rcInfiniteOpenGraph_adj_bond (ω : LatticeConfiguration) (b : LatticeBond) :
    (rcInfiniteOpenGraph ω).Adj b.source b.target ↔ latticeConfigurationBondState ω b = true := by
  rw [rcInfiniteOpenGraph_adj_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨b.adjacent, h⟩⟩

end PottsDiscontinuity.FK.Medial
