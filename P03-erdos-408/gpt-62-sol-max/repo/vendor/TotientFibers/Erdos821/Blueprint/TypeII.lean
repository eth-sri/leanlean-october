module

public import Erdos821.Blueprint.Candidate
public import Erdos821.Blueprint.Shift

@[expose] public section

noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace Erdos821.Blueprint
open Analytic

-- `determinant_forward` is proved in `Erdos821/S56/BlueprintDeterminant.lean`.

-- `determinant_converse` is proved in `Erdos821/S56/BlueprintDeterminant.lean`.

end Erdos821.Blueprint
