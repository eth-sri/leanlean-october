module

public import proofs.HordijkSteelThreshold.Gateway
public import proofs.HordijkSteelThreshold.PolymerCounts
public import proofs.RAF.Asymptotics.ReactionRatio
public import proofs.RAF.Concrete.Asymptotics
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

namespace HordijkSteelThreshold

open Filter Topology
open RAF.Polymer RAF.Concrete

theorem card_molecule_tendsto_atTop :
    Tendsto (fun n : Nat => Fintype.card (Molecule n)) atTop atTop := by
  refine Tendsto.congr' ?_ RAF.Asymptotics.binaryCardX_tendsto
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [card_molecules_exact]
  rfl

end HordijkSteelThreshold
