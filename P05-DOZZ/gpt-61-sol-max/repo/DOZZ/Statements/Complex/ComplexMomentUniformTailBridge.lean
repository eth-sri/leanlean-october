/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.HorizontalStrip
import DOZZ.Complex.Basic
import Batteries.Tactic.Alias

/-! The statement `DOZZ.complexMoment_uniform_tail_bridge`,
proved by `DOZZ.Proofs.complexMoment_uniform_tail_bridge`. -/

public section


namespace DOZZ

/-- Uniform tail-family Abelian boundary limit (see [KRV, Proposition 8.1]). A tail estimate only
for the limiting random variable is insufficient. Integrability is explicit on the eventually
positive moment exponents. -/
alias complexMoment_uniform_tail_bridge := DOZZ.Proofs.complexMoment_uniform_tail_bridge

end DOZZ
