import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.TerminalBase

/-! # The neutral terminal-fibre countability interface

The upper-bound target, independent of any particular counting producer or
cardinal/perfect-set application. The original `FinalHandoff` import reexports it.
-/

namespace VaughtConjecture.Knight
open Cardinal

/-- **Neutral per-rank fibre countability** — the actual upper-bound output.  Both the
quotient-local chain route and any alternative route (e.g. a failure-rooted receiver) land
here. -/
def CountableTerminalFibres : Prop :=
  ∀ ρ , ρ < (Cardinal.aleph 1).ord → #(TerminalClass ρ) ≤ Cardinal.aleph0

