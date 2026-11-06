module

public import proofs.HordijkSteelThreshold.Gateway
public import proofs.HordijkSteelThreshold.PolymerCounts
public import proofs.RAF.Concrete.Asymptotics

@[expose] public section

namespace HordijkSteelThreshold

open Filter RAF.Polymer

theorem card_molecule_tendsto_atTop :
    Tendsto (fun n : Nat => Fintype.card (Molecule n)) atTop atTop :=
  tendsto_atTop.mpr fun b => Filter.Eventually.mono
    (((tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < 2)).comp
      (tendsto_atTop_mono Nat.le_succ tendsto_id)) (eventually_ge_atTop (b + 2)))
    fun n hn => by rw [card_molecules_exact]; dsimp at hn; omega

end HordijkSteelThreshold
