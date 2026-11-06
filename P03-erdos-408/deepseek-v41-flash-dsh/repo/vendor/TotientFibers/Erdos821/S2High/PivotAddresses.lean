module

public import Erdos821.S2High.AddressHelpers

@[expose] public section

noncomputable section


namespace Erdos821.S2High



def birthBlockPivot {a : ℕ} (B : Finset (Fin a)) (hB : B.Nonempty) : Fin a :=
  Classical.choose hB

theorem birthBlockPivot_mem {a : ℕ} (B : Finset (Fin a)) (hB : B.Nonempty) :
    birthBlockPivot B hB ∈ B := Classical.choose_spec hB

end Erdos821.S2High
