module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# The ordinary class-group modulus
-/

namespace ClassFieldTheory

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The modulus with no finite exponent and no positivity condition.  Its ray
class group is the ordinary ideal class group. -/
def ordinaryRayClassModulus : RayClassModulus K where
  finitePart := 0
  infinitePart := ∅

/-- The ordinary class-group modulus is below every ray modulus. -/
theorem ordinaryRayClassModulus_le
    (m : RayClassModulus K) :
    ordinaryRayClassModulus K ≤ m := by
  constructor
  · positivity
  apply Finset.empty_subset

end ClassFieldTheory
