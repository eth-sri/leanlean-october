/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.BFScattered
public import VaughtConjecture.Knight.ExpansionDomainBF

@[expose] public section

namespace VaughtConjecture.Knight.ExpansionDomain

open FirstOrder Language Cardinal StoppingRankFiltration

/-- The countable restricted BF quotients give thinness without a Borel presentation. -/
theorem isThinOnNatModels_of_bfBoundedness (hct : CountableTerminalFibres) :
    knightSentence.IsThinOnNatModels :=
  isThinOn_of_bfScattered (fun _ => countable_bfEquivSetoid_quotient hct)

end VaughtConjecture.Knight.ExpansionDomain
