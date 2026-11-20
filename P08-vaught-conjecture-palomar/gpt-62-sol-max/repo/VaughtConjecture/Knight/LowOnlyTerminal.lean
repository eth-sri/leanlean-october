/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyNormalization
public import VaughtConjecture.Knight.CappedDonorLowHighNormalization

public import VaughtConjecture.Knight.TerminalProfile

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref

noncomputable section

variable {n K : ℕ} {P C : SemScheme n}

namespace Family

variable (F : Family P C K)

@[implicit_reducible]
def terminalContext : TerminalProfile.Context (State P C) (Field P C) where
  profile := State.profile
  admitted := F.Admissible
  clip c := State.map (min · c)
  clip_profile := fun c s => State.profile_map _ s
  clip_closed := fun {_ _ _} hj hv hb hs =>
    hs.map F (capWitness hv hb) hj (capWitness_reflects_bottom hb)
  norm := State.normalize
  norm_profile := State.profile_normalize
  norm_closed := fun {_ _} hj hs => F.normalize_admissible hj hs

end Family

end

end VaughtConjecture.Knight.LowOnly
