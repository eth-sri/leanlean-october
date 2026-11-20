module

public import proofs.RAF.Concrete.UniformModel

@[expose] public section

namespace RAF.Concrete

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer

def HasRAFEvent (n : Nat) : Set (CatalysisSample n) :=
  {ω | ∃ S : Finset (Reaction n),
    IsRevRAF (binaryPolymerCRS n 2) (catalysisOf ω) S}

theorem measurableSet_hasRAFEvent (n : Nat) : MeasurableSet (HasRAFEvent n) := by
  exact Set.toFinite (HasRAFEvent n) |>.measurableSet

end RAF.Concrete
