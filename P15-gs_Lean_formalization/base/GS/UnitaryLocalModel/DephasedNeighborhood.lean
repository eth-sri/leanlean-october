module

public import GS.UnitaryLocalModel.DephasedChart
public import GS.UnitaryLocalModel.ZeroLevelChart

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Open-neighbourhood coverage of the dephased unitary chart

The chart image is an open neighbourhood in the full dephased slice, with
its inherited matrix topology. The inverse is the continuous restriction
of the actual implicit-function chart; no coverage assumption is imposed.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryManifold Set
open scoped Topology
namespace GS.UnitaryLocalModel
variable {q : ℕ}

def dephasedBase (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : DephasedUnitary Q o :=
  ⟨Q, (by simpa [anchorConstraints] using anchorConstraints_zero Q o hQ),
    anchorPositive_self Q.val o hQ⟩

def dephasedChartSource (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : Set (DephasedUnitary Q o) :=
  {A | A.val ∈ (unitaryConstraintChart Q o hQ).source}

theorem dephasedChartSource_open (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : IsOpen (dephasedChartSource Q o hQ) :=
  (unitaryConstraintChart Q o hQ).open_source.preimage continuous_subtype_val

theorem base_mem_dephasedChartSource (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    dephasedBase Q o hQ ∈ dephasedChartSource Q o hQ :=
  base_mem_unitaryConstraintChart_source Q o hQ

def dephasedCoordinates (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o) : DephasedModel Q o :=
  (unitaryConstraintChart Q o hQ A.val).2

theorem unitaryConstraintChart_of_dephased (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o)
    (hA : A ∈ dephasedChartSource Q o hQ) :
    unitaryConstraintChart Q o hQ A.val = (0, dephasedCoordinates Q o hQ A) := by
  apply Prod.ext
  · rw [unitaryConstraintChart_fst Q o hQ A.val hA]
    exact A.property.1
  · rfl

theorem dephasedParametrization_coordinates (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o)
    (hA : A ∈ dephasedChartSource Q o hQ) :
    dephasedParametrization Q o hQ (dephasedCoordinates Q o hQ A) = A.val.val := by
  unfold dephasedParametrization
  rw [← unitaryConstraintChart_of_dephased Q o hQ A hA,
    (unitaryConstraintChart Q o hQ).left_inv hA]

/-- The actual homeomorphism between open subsets of the inherited slice
and the real constraint kernel. -/
def dephasedChartHomeomorph (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    dephasedChartSource Q o hQ ≃ₜ dephasedChartDomain Q o hQ :=
  zeroLevelHomeomorph (unitaryConstraintChart Q o hQ)
    (fun A => anchorImag Q.val o A.val = 0 ∧ AnchorPositive Q.val A.val o)
    (by
      intro A hA
      rw [unitaryConstraintChart_fst Q o hQ A hA]
      have hp := ((unitaryConstraintChart_source_iff Q o hQ A).mp hA).2.2
      simp only [hp, and_true])

end GS.UnitaryLocalModel
