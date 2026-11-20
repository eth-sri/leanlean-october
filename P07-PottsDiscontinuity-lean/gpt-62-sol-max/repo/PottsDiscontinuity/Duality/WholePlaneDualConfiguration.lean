/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.WholePlaneDualGraph
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace PottsDiscontinuity.FK.Medial

open PottsDiscontinuity.FK

noncomputable section

def wholePlaneBondEdgeEquiv : LatticeBond ≃ squareLattice.edgeSet :=
  Equiv.ofBijective latticeBondEdge ⟨fun _ _ h => LatticeBond.toSym2_injective (congrArg Subtype.val h),
    fun e => by
      have h : squareLattice.Adj e.1.out.1 e.1.out.2 := by
        grind [Quot.out_eq, squareLattice.mem_edgeSet.mp]
      obtain ⟨b, hb⟩ := LatticeBond.exists_of_adj h
      exact ⟨b, Subtype.ext (hb.trans (Quot.out_eq e.1))⟩⟩

def wholePlaneDualCrossingEdgeEquiv : squareLattice.edgeSet ≃ squareLattice.edgeSet where
  toFun e := wholePlaneBondEdgeEquiv (primalBondOfDual (wholePlaneBondEdgeEquiv.symm e))
  invFun e := wholePlaneBondEdgeEquiv (dualBondOfPrimal (wholePlaneBondEdgeEquiv.symm e))
  left_inv e := by
    simp
  right_inv e := by
    simp

def boolComplementEquiv : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by simp
  right_inv b := by simp

def boolComplementHomeomorph : Bool ≃ₜ Bool where
  toEquiv := boolComplementEquiv
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- The actual edge-state dual transform: each dual edge receives the
complement of its crossing primal edge state. -/
def wholePlaneDualConfigurationHomeomorph :
    LatticeConfiguration ≃ₜ LatticeConfiguration := by
  let hindices : squareLattice.edgeSet ≃ squareLattice.edgeSet :=
    wholePlaneDualCrossingEdgeEquiv.symm
  exact (Homeomorph.piCongrLeft (Y := fun _ : squareLattice.edgeSet => Bool) hindices).trans
    (Homeomorph.piCongrRight fun _ : squareLattice.edgeSet => boolComplementHomeomorph)

@[simp] theorem wholePlaneDualConfigurationHomeomorph_apply
    (ω : LatticeConfiguration) (e : squareLattice.edgeSet) :
    wholePlaneDualConfigurationHomeomorph ω e =
      Bool.not (ω (wholePlaneDualCrossingEdgeEquiv e)) := by
  simp [wholePlaneDualConfigurationHomeomorph, boolComplementHomeomorph, boolComplementEquiv, Homeomorph.piCongrLeft, Equiv.piCongrLeft]

@[simp] theorem wholePlaneDualConfigurationHomeomorph_bondState
    (ω : LatticeConfiguration) (d : LatticeBond) :
    latticeConfigurationBondState (wholePlaneDualConfigurationHomeomorph ω) d =
      Bool.not (latticeConfigurationBondState ω (primalBondOfDual d)) := by
  change wholePlaneDualConfigurationHomeomorph ω (latticeBondEdge d) =
    Bool.not (ω (latticeBondEdge (primalBondOfDual d)))
  rw [wholePlaneDualConfigurationHomeomorph_apply]
  change Bool.not (ω (wholePlaneBondEdgeEquiv (primalBondOfDual
    (wholePlaneBondEdgeEquiv.symm (wholePlaneBondEdgeEquiv d))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem wholePlaneDualConfigurationHomeomorph_measurable :
    Measurable wholePlaneDualConfigurationHomeomorph :=
  wholePlaneDualConfigurationHomeomorph.continuous_toFun.measurable

end
end PottsDiscontinuity.FK.Medial
