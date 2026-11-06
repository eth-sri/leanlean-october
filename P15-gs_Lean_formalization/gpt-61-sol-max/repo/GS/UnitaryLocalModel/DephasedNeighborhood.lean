
import GS.UnitaryLocalModel.DephasedChart
import GS.UnitaryLocalModel.ZeroLevelChart



/-!
# Open-neighbourhood coverage of the dephased unitary chart

The chart image is an open neighbourhood in the full dephased slice, with
its inherited matrix topology. The inverse is the continuous restriction
of the actual implicit-function chart; no coverage assumption is imposed.
-/
noncomputable section
namespace GS.UnitaryLocalModel

variable (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o)

def dephasedBase : DephasedUnitary Q o :=
  ⟨Q, (by simpa [anchorConstraints] using anchorConstraints_zero Q o hQ),
    anchorPositive_self Q.val o hQ⟩

def dephasedChartSource : Set (DephasedUnitary Q o) :=
  {A | A.val ∈ (unitaryConstraintChart Q o hQ).source}

theorem dephasedChartSource_open : IsOpen (dephasedChartSource Q o hQ) :=
  (unitaryConstraintChart Q o hQ).open_source.preimage continuous_subtype_val

theorem base_mem_dephasedChartSource :
    dephasedBase Q o hQ ∈ dephasedChartSource Q o hQ :=
  base_mem_unitaryConstraintChart_source Q o hQ

variable (A : DephasedUnitary Q o)

def dephasedCoordinates  : DephasedModel Q o :=
  (unitaryConstraintChart Q o hQ A.val).2



theorem dephasedParametrization_coordinates 
    (hA : A ∈ dephasedChartSource Q o hQ) :
    dephasedParametrization Q o hQ (dephasedCoordinates Q o hQ A) = A.val.val := by
  unfold dephasedParametrization
  have he : unitaryConstraintChart Q o hQ A.val = (0,dephasedCoordinates Q o hQ A) :=
    Prod.ext ((unitaryConstraintChart_fst Q o hQ A.val hA).trans A.property.1) rfl
  rw [← he,(unitaryConstraintChart Q o hQ).left_inv hA]

/-- The actual homeomorphism between open subsets of the inherited slice
and the real constraint kernel. -/
def dephasedChartHomeomorph :
    dephasedChartSource Q o hQ ≃ₜ dephasedChartDomain Q o hQ :=
  zeroLevelHomeomorph (unitaryConstraintChart Q o hQ)
    (fun A => anchorImag Q.val o A.val = 0 ∧ AnchorPositive Q.val A.val o)
    (by simp_all [unitaryConstraintChart_fst,unitaryConstraintChart_source_iff,and_true])

end GS.UnitaryLocalModel
