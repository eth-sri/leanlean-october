
import proofs.HordijkSteelThreshold.Gateway
import proofs.HordijkSteelThreshold.PolymerCounts
import proofs.RAF.Polymer.Reactions
import proofs.RAF.Concrete.UniformModel
import proofs.RAF.Core.CRS
import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv




namespace RAF.Concrete

open RAF.Polymer

variable (n : Nat)

def HasRAFEvent   :=
  {ω | ∃ S : Finset (Reaction n),
    IsRevRAF (binaryPolymerCRS n 2) (catalysisOf ω) S}



end RAF.Concrete

namespace HordijkSteelThreshold

open Filter
open RAF.Polymer

theorem card_molecule_tendsto_atTop :
    Tendsto (fun n : Nat => Fintype.card (Molecule n)) atTop atTop := by
  refine tendsto_atTop_mono ?_ tendsto_id
  intro n
  change n ≤ _
  rw [card_molecules_exact, pow_succ]
  have := Nat.lt_two_pow_self (n := n)
  omega

end HordijkSteelThreshold
