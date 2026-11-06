/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionPoleFree
import DOZZ.Brownian.Reflection.MomentAssembly
import Batteries.Tactic.Alias

/-! The statement `DOZZ.lastone_brownian_smallPower_limit`,
proved by `DOZZ.Proofs.lastone_brownian_smallPower_limit`. -/

public section


namespace DOZZ

/-- The law-level Brownian/GMC input to [KRV, Lemma 10.6], with small power `ν/γ`. The local
epsilon domain and zero-mode evaluation are handled in `structureConstant_lastone_limit`;
this declaration states only the conditioned integral limit. -/
alias lastone_brownian_smallPower_limit := DOZZ.Proofs.lastone_brownian_smallPower_limit

end DOZZ
