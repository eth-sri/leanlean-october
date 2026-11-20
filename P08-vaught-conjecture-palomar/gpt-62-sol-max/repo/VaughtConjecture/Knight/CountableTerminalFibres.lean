/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TerminalBase

@[expose] public section

namespace VaughtConjecture.Knight

open Cardinal

/-- **Neutral per-rank fibre countability** — the actual upper-bound output.  Both the
quotient-local chain route and any alternative route (e.g. a failure-rooted receiver) land
here. -/
def CountableTerminalFibres : Prop :=
  ∀ ρ : Ordinal.{0}, ρ < (Cardinal.aleph 1).ord → #(TerminalClass ρ) ≤ Cardinal.aleph0

end VaughtConjecture.Knight
