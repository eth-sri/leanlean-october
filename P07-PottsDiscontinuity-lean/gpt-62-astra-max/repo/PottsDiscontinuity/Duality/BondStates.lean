/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Only bond states and actual primal graphs are retained. -/
module

public import PottsDiscontinuity.Duality.LatticePorts
public import PottsDiscontinuity.FK.BoxLaw

@[expose] public section

namespace PottsDiscontinuity.FK.Medial

/-- The square-lattice edge underlying a normalized actual lattice bond. -/
def latticeBondEdge (b : LatticeBond) : squareLattice.edgeSet :=
  ⟨b.toSym2, b.toSym2_mem_edgeSet⟩

variable (ω : LatticeConfiguration) (b : LatticeBond)
include ω

include b in
/-- Read the actual original-edge state at a bond, without introducing a second
configuration carrier. -/
def latticeConfigurationBondState : Bool :=
  ω (latticeBondEdge b)

/-- The literal open primal graph read from the existing unordered edge-state
carrier. -/
def wholePlaneOpenPrimalGraph : SimpleGraph LatticeVertex where
  Adj u v := ∃ h : squareLattice.Adj u v,
    ω ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true
  symm := ⟨by
    intro u v h
    rcases h with ⟨h, hopen⟩
    refine ⟨h.symm, ?_⟩
    have hedge : (⟨s(v, u), squareLattice.mem_edgeSet.mpr h.symm⟩ : squareLattice.edgeSet) =
        ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ := by
      apply Subtype.ext
      exact Sym2.eq_swap
    rw [hedge]
    exact hopen⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨h, _⟩
    exact squareLattice.loopless.irrefl u h⟩

theorem wholePlaneOpenPrimalGraph_adj_bond :
    (wholePlaneOpenPrimalGraph ω).Adj b.source b.target ↔
      latticeConfigurationBondState ω b = true := by
  constructor
  · rintro ⟨_, h⟩
    assumption
  · intro h
    exact ⟨b.adjacent, by assumption⟩

end PottsDiscontinuity.FK.Medial
