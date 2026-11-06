/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.NormalizedProfileFamily
public import VaughtConjecture.Knight.GradeOneSectionLifting

set_option linter.privateModule false

/-! # Uniform original-cap lifting for normalized finite profile families

The controller is constructed from the input order/refinement laws. The
output again has those laws by `NormalizedProfileFamily.family`, so the
algebraic construction may be reapplied. No support-plan assembly, nonbottom
higher-grade controller, guarded forcing, or legal successor is asserted.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.NormalizedProfileLifting

open Transform Value ExtOrd SlotControllerFamily FullRowLifting
open NormalizedProfileFamily SlotPatternRefinement

local notation "rankCode" => NormalizedProfileFamily.code

variable {X : Type*} [Fintype X] (L : OrderLaw X)

end VaughtConjecture.Knight.NormalizedProfileLifting
