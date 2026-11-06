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

section
variable (ω : LatticeConfiguration)
/-- Read the actual original-edge state at a bond, without introducing a second
configuration carrier. -/
def latticeConfigurationBondState (b : LatticeBond) : Bool :=
  ω (latticeBondEdge b)

@[simp] theorem latticeConfigurationBondState_eq (b : LatticeBond) :
    latticeConfigurationBondState ω b = ω ⟨b.toSym2, b.toSym2_mem_edgeSet⟩ := rfl

/-- The literal open primal graph read from the existing unordered edge-state
carrier. -/
def wholePlaneOpenPrimalGraph  : SimpleGraph LatticeVertex where
  Adj u v := ∃ h : squareLattice.Adj u v,
    ω ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true
  symm := ⟨by
    intro u v h
    rcases h with ⟨h, hopen⟩
    refine ⟨h.symm, ?_⟩
    grind⟩
  loopless := ⟨by
    simp⟩


theorem wholePlaneOpenPrimalGraph_adj_bond (b : LatticeBond) :
    (wholePlaneOpenPrimalGraph ω).Adj b.source b.target ↔
      latticeConfigurationBondState ω b = true := by
  constructor
  · rintro ⟨_, h⟩
    tauto
  · intro h
    exact ⟨b.adjacent, by tauto⟩
end

end PottsDiscontinuity.FK.Medial
