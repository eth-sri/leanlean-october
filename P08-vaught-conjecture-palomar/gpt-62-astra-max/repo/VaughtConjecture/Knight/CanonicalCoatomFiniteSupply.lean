/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomRecursiveOrdered

/-! # Constructed maximal coatom amalgamation at every arity

The two small seeds and initialized grade recursion give the actual finite
supplier. The Henkin and spectrum applications remain in `CanonicalCoatomSupply`,
which reexports this producer. No model-existence consumer is imported here.
-/
@[expose] public section

namespace VaughtConjecture.Knight.CanonicalCoatomSupply
open Transform Value ExtOrd AmalgamationPlan SemSchemeBoundaryInput
noncomputable section

/-- The finite supplier, with no completion or lifting assumptions on an output. -/
theorem supply {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) :
    MaximalCoatomAmalgamationSupply α := by
  intro n C pa pb h
  exact CoatomRecursiveOrdered.exists_amalgam hα C h

end
end VaughtConjecture.Knight.CanonicalCoatomSupply
