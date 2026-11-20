/- One positive section produces the negative section through an explicit
involutive ledger reversal. Generic conditional statement; no native gate
or section/rank producer is asserted. -/
module
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Continuous
public import Mathlib.Basic.Real.Basic
@[expose] public section
namespace Glennie.RobustBranchCore

variable {X L : Type*}

def reversalSection (reverse : X → X) (tau : L → L) (positiveSection : L → X) :
    L → X := fun b => reverse (positiveSection (tau b))

section Topology
variable [TopologicalSpace X] [TopologicalSpace L]

end Topology
end Glennie.RobustBranchCore
