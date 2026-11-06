module

public import GS.UnitaryLocalModel.DephasedChart
public import GS.UnitaryLocalModel.ZeroLevelChart

@[expose] public section


/-!
# Open-neighbourhood coverage of the dephased unitary chart

The chart image is an open neighbourhood in the full dephased slice, with
its inherited matrix topology. The inverse is the continuous restriction
of the actual implicit-function chart; no coverage assumption is imposed.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GS.UnitaryLocalModel
variable {q : ℕ}

section
variable (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o)
def dephasedBase : DephasedUnitary Q o :=
  ⟨Q, (by simpa [anchorConstraints] using anchorConstraints_zero Q o hQ),
    anchorPositive_self Q.val o hQ⟩

def dephasedChartSource : Set (DephasedUnitary Q o) :=
  {A | A.val ∈ (unitaryConstraintChart Q o hQ).source}

theorem dephasedChartSource_open : IsOpen (dephasedChartSource Q o hQ) :=
  (unitaryConstraintChart Q o hQ).open_source.preimage continuous_subtype_val

def dephasedCoordinates (A : DephasedUnitary Q o) : DephasedModel Q o :=
  (unitaryConstraintChart Q o hQ A.val).2

theorem dephasedParametrization_coordinates (A : DephasedUnitary Q o)
    (hA : A ∈ dephasedChartSource Q o hQ) :
    dephasedParametrization Q o hQ (dephasedCoordinates Q o hQ A) = A.val.val := by
  rw [dephasedParametrization, ← show unitaryConstraintChart Q o hQ A.val = (0, dephasedCoordinates Q o hQ A) from
    Prod.ext (by rw [unitaryConstraintChart_fst Q o hQ A.val hA]; grind) rfl, (unitaryConstraintChart Q o hQ).left_inv hA]

end

end GS.UnitaryLocalModel
