module

public import GS.UnitaryLocalModel.FullCoverageCoordinates
public import GS.UnitaryLocalModel.TopologyFeasibility
public import GS.Continuation.CompactCoverageTools

@[expose] public section


/-!
# Coverage of an actual neighbourhood in the complete unitary family

Every representative of the full compact scalar-block fibre lies in the
normalization maps this open set into the compact local model. Compactness
then provides an ambient open neighbourhood whose intersection with the
original matrix family is covered. No chosen-branch coverage is assumed.
-/
noncomputable section
open Matrix GS GS.UnitaryNonmanifold GS.NonmanifoldCompletion Set
namespace GS.UnitaryLocalModel
variable {q : ℕ}

end GS.UnitaryLocalModel
