module

public import proofs.RAF.Concrete.UniformModel

@[expose] public section

namespace RAF.Concrete

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer

variable (n : Nat)

def HasRAFEvent  : Set (CatalysisSample n) :=
  {ω | ∃ S : Finset $ Reaction n,
    IsRevRAF (binaryPolymerCRS n 2) (catalysisOf ω) S}

theorem measurableSet_hasRAFEvent  : MeasurableSet (HasRAFEvent n) := by
  exact Set.toFinite (HasRAFEvent n) |>.measurableSet

end RAF.Concrete
