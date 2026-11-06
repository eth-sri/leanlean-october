module

public import Erdos821.S2High.AddressHelpers

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos821.S2High

open Erdos821.Blueprint.Graph

def birthBlockPivot {a } (B : Finset (Fin a)) (hB : B.Nonempty)  :=
  Classical.choose hB

theorem birthBlockPivot_mem {a : ℕ} (B : Finset (Fin a)) (hB : B.Nonempty) :
    birthBlockPivot B hB ∈ B := Classical.choose_spec hB

end Erdos821.S2High
