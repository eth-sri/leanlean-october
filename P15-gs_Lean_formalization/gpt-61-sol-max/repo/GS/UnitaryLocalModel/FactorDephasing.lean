
import GS.UnitaryLocalModel.DephasedNeighborhood
import GS.UnitaryLocalModel.DephasingTopology
import GS.UnitaryLocalModel.FactorSpace
import GS.UnitaryLocalModel.NormalizationBaseFibre



/-!
# Continuous dephased cores on the full compact factor space

The nonzero-anchor condition cuts out an open subset of the full factor
space. Both normalized middle factors are continuous maps into the genuine
dephased unitary slice, with its inherited matrix topology.
-/

noncomputable section
namespace GS.UnitaryLocalModel

variable (Q : FullUnitary q) (o : Fin q)

def anchorFactorSet : Set (SmallFactorSpace q) :=
  {p | AnchorNonzero Q.val p.val.2.1 o ∧ AnchorNonzero Q.val p.val.2.2.1 o}

theorem anchorFactorSet_open :
    IsOpen (anchorFactorSet Q o) := ((isOpen_anchorNonzero Q.val o).preimage (by fun_prop)).inter
    ((isOpen_anchorNonzero Q.val o).preimage (by fun_prop))

variable (p : anchorFactorSet Q o)

def dephasedFirst  : DephasedUnitary Q o :=
  ⟨fullUnitary (dephase Q.val p.val.val.2.1 o)
      (dephase_unitary p.val.property.2.1 p.property.1),
    (dephased_constraints_iff _ _ _).mpr
      ⟨dephase_anchor_column_positive p.property.1,
        dephase_anchor_row_positive p.property.1⟩⟩

def dephasedSecond  : DephasedUnitary Q o :=
  ⟨fullUnitary (dephase Q.val p.val.val.2.2.1 o)
      (dephase_unitary p.val.property.2.2.1 p.property.2),
    (dephased_constraints_iff _ _ _).mpr
      ⟨dephase_anchor_column_positive p.property.2,
        dephase_anchor_row_positive p.property.2⟩⟩





theorem continuous_dephasedFirst :
    Continuous (dephasedFirst Q o) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply ContinuousAt.codRestrict
  apply ContinuousAt.codRestrict
  exact ContinuousAt.comp (f := fun p : anchorFactorSet Q o => p.val.val.2.1)
    (continuousAt_dephase p.property.1) (by fun_prop)

theorem continuous_dephasedSecond :
    Continuous (dephasedSecond Q o) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply ContinuousAt.codRestrict
  apply ContinuousAt.codRestrict
  exact ContinuousAt.comp (f := fun p : anchorFactorSet Q o => p.val.val.2.2.1)
    (continuousAt_dephase p.property.2) (by fun_prop)

end GS.UnitaryLocalModel
