module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
public import ClassFieldTheory.KroneckerWeber.RationalRayClassFieldCyclotomic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Arithmetic reciprocity for rational cyclotomic ray class fields

This module uses an ordinary rational uniformizer, not its inverse, and
the arithmetic global norm-residue map.  Consequently an unramified
prime `q` acts on roots of unity by the direct power `q`.  The finite
Galois/ray-class comparison is retained as a `ContinuousMulEquiv` with
the native quotient and finite Krull topologies.
-/

open scoped Classical IsMulCommutative NumberField Cyclotomic

noncomputable section

namespace KroneckerWeber

open GlobalClassFieldTheory
open GlobalClassFieldTheory.GlobalClassFields
open GlobalClassFieldTheory.Reciprocity




































section NonzeroOrder

variable (m : ℕ) [NeZero m]

local instance : NeZero (m : ℚ) :=
  ⟨by exact_mod_cast (NeZero.ne m)⟩

noncomputable local instance :
    NumberField
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨m, NeZero.pos m⟩















































































































































































end NonzeroOrder

end KroneckerWeber

end
