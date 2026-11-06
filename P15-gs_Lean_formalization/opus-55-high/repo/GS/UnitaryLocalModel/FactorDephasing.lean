module

public import GS.UnitaryLocalModel.DephasedNeighborhood
public import GS.UnitaryLocalModel.DephasingTopology
public import GS.UnitaryLocalModel.FactorSpace
public import GS.UnitaryLocalModel.NormalizationBaseFibre

@[expose] public section


/-!
# Continuous dephased cores on the full compact factor space

The nonzero-anchor condition cuts out an open subset of the full factor
space. Both normalized middle factors are continuous maps into the genuine
dephased unitary slice, with its inherited matrix topology.
-/

noncomputable section
open Matrix GS GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel
variable {q : ℕ}

section
variable (Q : FullUnitary q) (o : Fin q)
def anchorFactorSet : Set (SmallFactorSpace q) :=
  {p | AnchorNonzero Q.val p.val.2.1 o ∧ AnchorNonzero Q.val p.val.2.2.1 o}

theorem anchorFactorSet_open :
    IsOpen (anchorFactorSet Q o) :=
  ((isOpen_anchorNonzero Q.val o).preimage (by fun_prop)).inter
    ((isOpen_anchorNonzero Q.val o).preimage (by fun_prop))

def dephasedFirst (p : anchorFactorSet Q o) : DephasedUnitary Q o :=
  ⟨fullUnitary (dephase Q.val p.val.val.2.1 o)
      (dephase_unitary p.val.property.2.1 p.property.1),
    (dephased_constraints_iff _ _ _).mpr
      ⟨dephase_anchor_column_positive p.property.1,
        dephase_anchor_row_positive p.property.1⟩⟩

def dephasedSecond (p : anchorFactorSet Q o) : DephasedUnitary Q o :=
  ⟨fullUnitary (dephase Q.val p.val.val.2.2.1 o)
      (dephase_unitary p.val.property.2.2.1 p.property.2),
    (dephased_constraints_iff _ _ _).mpr
      ⟨dephase_anchor_column_positive p.property.2,
        dephase_anchor_row_positive p.property.2⟩⟩



theorem continuous_dephased :
    Continuous (dephasedFirst Q o) ∧ Continuous (dephasedSecond Q o) := by
  constructor <;> refine .subtype_mk (.subtype_mk (continuous_iff_continuousAt.2 fun p => ?_) _) _
  exacts [(continuousAt_dephase p.2.1).comp (f := fun p : anchorFactorSet Q o => p.val.val.2.1) (by fun_prop),
    (continuousAt_dephase p.2.2).comp (f := fun p : anchorFactorSet Q o => p.val.val.2.2.1) (by fun_prop)]

end

end GS.UnitaryLocalModel
