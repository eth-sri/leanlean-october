/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthNormalization
public import VaughtConjecture.Knight.CappedDonorRepairPackage
public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.CappedDonorLowHighNormalization
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.TerminalProfile

@[expose] public section

namespace VaughtConjecture.Knight.Growth

open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref

open CanonicalPairedInverse

noncomputable section

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}

variable (X : RelativeData DA semA DQ semQ)

@[implicit_reducible]
def terminalContext : TerminalProfile.Context (State DA DQ) (Field DA DQ) where
  profile := State.profile
  admitted := Admitted X
  clip c := State.map (min · c)
  clip_profile := fun c s => State.profile_map _ s
  clip_closed := fun {_ _ _} hj hv hb hs =>
    hs.map_on_profile X (capWitness hv hb) hj (fun _ => capWitness_reflects_bottom hb _)
  norm := State.normalize
  norm_profile := State.profile_normalize
  norm_closed := fun {_ _} hj hs => normalize_admitted X hj hs

end

end VaughtConjecture.Knight.Growth
