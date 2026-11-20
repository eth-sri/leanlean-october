module

public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.EmbedsInRayClassFieldIffConductorLe
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Existence of the abelian conductor

The conductor of a finite abelian extension is the least modulus whose ray
class field contains that extension. The older theorem name
`embedsInRayClassField_iff_conductor_le` remains available for compatibility;
its conclusion is an existence statement, so this name reflects its type.
-/

namespace ClassFieldTheory

/-- A finite abelian extension of number fields has a conductor. -/
alias exists_abelianConductor := embedsInRayClassField_iff_conductor_le

end ClassFieldTheory
