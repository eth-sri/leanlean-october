/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.WholePlaneDualGraph
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace PottsDiscontinuity.FK.Medial



noncomputable section

def dualEdgeFirst (e : squareLattice.edgeSet)  := e.1.out.1
def dualEdgeSecond (e : squareLattice.edgeSet)  := e.1.out.2

 theorem edgeSet_out_adj (e : squareLattice.edgeSet) :
    squareLattice.Adj (dualEdgeFirst e) (dualEdgeSecond e) := by
  have hrepr : s(dualEdgeFirst e, dualEdgeSecond e) = e.1 := Quot.out_eq _
  exact squareLattice.mem_edgeSet.mp (hrepr ▸ e.2)

def wholePlaneBondEdgeEquiv : LatticeBond ≃ squareLattice.edgeSet where
  toFun := latticeBondEdge
  invFun e := Classical.choose
    (LatticeBond.existsUnique_of_adj (edgeSet_out_adj e))
  left_inv b := by
    change Classical.choose
      (LatticeBond.existsUnique_of_adj (edgeSet_out_adj (latticeBondEdge b))) = b
    
    
    exact ((Classical.choose_spec
              (LatticeBond.existsUnique_of_adj (edgeSet_out_adj (latticeBondEdge b)))).2 b (by
                       change b.toSym2 = s((latticeBondEdge b).1.out.1,
                         (latticeBondEdge b).1.out.2)
                       exact (Quot.out_eq (latticeBondEdge b).1).symm)).symm
  right_inv e := by
    apply Subtype.ext
    
    exact (Classical.choose_spec
             (LatticeBond.existsUnique_of_adj (edgeSet_out_adj e))).1.trans (Quot.out_eq e.1)

def wholePlaneDualCrossingEdgeEquiv : squareLattice.edgeSet ≃ squareLattice.edgeSet where
  toFun e := wholePlaneBondEdgeEquiv (primalBondOfDual (wholePlaneBondEdgeEquiv.symm e))
  invFun e := wholePlaneBondEdgeEquiv (dualBondOfPrimal (wholePlaneBondEdgeEquiv.symm e))
  left_inv e := by
    simp_all
  right_inv e := by
    simp_all

def boolComplementEquiv : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

def boolComplementHomeomorph : Bool ≃ₜ Bool where
  toEquiv := boolComplementEquiv
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- The actual edge-state dual transform: each dual edge receives the
complement of its crossing primal edge state. -/
def wholePlaneDualConfigurationHomeomorph :
    LatticeConfiguration ≃ₜ LatticeConfiguration := (Homeomorph.piCongrLeft (Y := fun _ : squareLattice.edgeSet => Bool)  wholePlaneDualCrossingEdgeEquiv.symm ).trans
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
  
  rw [(by
         
         change wholePlaneBondEdgeEquiv (primalBondOfDual
           (wholePlaneBondEdgeEquiv.symm (wholePlaneBondEdgeEquiv d))) = _
         rw [Equiv.symm_apply_apply]
         rfl : wholePlaneDualCrossingEdgeEquiv (latticeBondEdge d) =
      latticeBondEdge (primalBondOfDual d))]



private theorem bond_endpoints_of_toSym2_eq (b : LatticeBond) (u v : LatticeVertex)
    (h : b.toSym2 = s(u, v)) :
     b.source = u ∧ b.target = v  ∨  b.source = v ∧ b.target = u  := Sym2.eq_iff.mp h

/-- The open primal graph after the actual dual transform is exactly the
closed-dual graph of the original configuration. -/
theorem wholePlaneOpenPrimalGraph_dualConfiguration_eq (ω : LatticeConfiguration) :
    wholePlaneOpenPrimalGraph (wholePlaneDualConfigurationHomeomorph ω) =
      wholePlaneClosedDualGraph ω := by
  ext u v
  constructor
  · intro h
    
    rcases h with ⟨hadj, hopen⟩
    obtain ⟨d, hd, _⟩ := LatticeBond.existsUnique_of_adj hadj
    have hedge : latticeBondEdge d =
        ⟨s(u, v), squareLattice.mem_edgeSet.mpr hadj⟩ := Subtype.ext hd
    rw [← hedge] at hopen
    change latticeConfigurationBondState
      (wholePlaneDualConfigurationHomeomorph ω) d = true at hopen
    
    
    obtain hdir | hdir := bond_endpoints_of_toSym2_eq d u v hd
    · exact (wholePlaneClosedDualGraph_adj_iff_dualBond ω u v).mpr
        ⟨d,  by
               simp_all , Or.inl ⟨hdir.1.symm, hdir.2.symm⟩⟩
    · exact (wholePlaneClosedDualGraph_adj_iff_dualBond ω u v).mpr
        ⟨d,  by
               simp_all , Or.inr ⟨hdir.2.symm, hdir.1.symm⟩⟩
  · intro h
    obtain ⟨d, hclosed, hdir⟩ :=
      (wholePlaneClosedDualGraph_adj_iff_dualBond ω u v).mp h
    
    
    have hbond := (wholePlaneOpenPrimalGraph_adj_bond
      (wholePlaneDualConfigurationHomeomorph ω) d).2 (by
                                                        grind [wholePlaneDualConfigurationHomeomorph_bondState])
    rcases hdir with huv | huv
    · simpa [huv.1, huv.2] using hbond
    · simpa [huv.1, huv.2] using hbond.symm



theorem wholePlaneDualConfigurationHomeomorph_measurable :
    Measurable wholePlaneDualConfigurationHomeomorph :=
  wholePlaneDualConfigurationHomeomorph.continuous_toFun.measurable

end
end PottsDiscontinuity.FK.Medial
