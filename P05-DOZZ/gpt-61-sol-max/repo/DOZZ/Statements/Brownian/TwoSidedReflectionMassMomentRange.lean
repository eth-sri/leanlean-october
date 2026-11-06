/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Brownian.TwoSided.TwoSidedReflectionMassMomentRange
import Batteries.Tactic.Alias

/-! The statement `DOZZ.twoSidedReflectionMass_moment_range`,
proved by `DOZZ.Proofs.twoSidedReflectionMass_moment_range`. -/

public section


namespace DOZZ

/-- The two-sided conditioned integral has every real moment below `4/γ²`, locally uniformly on
compact positive-drift and strict subcritical parameter ranges. See [KRV, Lemma 3.3] and its
proof in [KRV, §12.3]. -/
alias twoSidedReflectionMass_moment_range := DOZZ.Proofs.twoSidedReflectionMass_moment_range

end DOZZ
