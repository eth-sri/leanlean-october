/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Only bond states and actual primal graphs are retained. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.LatticePorts
public import PottsDiscontinuity.FK.BoxLaw

@[expose] public section

namespace PottsDiscontinuity.FK.Medial

/-- The square-lattice edge underlying a normalized actual lattice bond. -/
def latticeBondEdge (b : LatticeBond) : squareLattice.edgeSet :=
  ⟨b.toSym2, b.toSym2_mem_edgeSet⟩

/-- Read the actual original-edge state at a bond, without introducing a second
configuration carrier. -/
def latticeConfigurationBondState (ω : LatticeConfiguration) (b : LatticeBond)  :=
  ω (latticeBondEdge b)



/-- The literal open primal graph read from the existing unordered edge-state
carrier. -/
def wholePlaneOpenPrimalGraph (ω : LatticeConfiguration) : SimpleGraph LatticeVertex where
  Adj u v := ∃ h : squareLattice.Adj u v,
    ω ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true
  symm := ⟨by
    intro u v h
    rcases h with ⟨h, hopen⟩
    refine ⟨h.symm, ?_⟩
    all_goals grind⟩
  loopless := ⟨by
    simp_all⟩



theorem wholePlaneOpenPrimalGraph_adj_bond (ω : LatticeConfiguration) (b : LatticeBond) :
    (wholePlaneOpenPrimalGraph ω).Adj b.source b.target ↔
      latticeConfigurationBondState ω b = true := by
  constructor
  · rintro ⟨_, h⟩
    aesop
  · intro h
    exact ⟨b.adjacent, h⟩

end PottsDiscontinuity.FK.Medial
