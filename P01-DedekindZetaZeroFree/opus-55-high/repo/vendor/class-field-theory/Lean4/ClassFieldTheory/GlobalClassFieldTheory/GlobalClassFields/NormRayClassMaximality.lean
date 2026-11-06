module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Exact narrow finite ray-class presentations of norm quotients

For every finite Galois extension, the ray class group at the exact narrow
finite conductor surjects onto the actual idèle-class norm quotient.  This
file characterizes when that presentation has no residual kernel: the norm
subgroup is then exactly the congruence subgroup at its narrow finite
conductor, equivalently the two finite quotient groups have the same order.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

/-- Canonical class-group commutativity supplies normality for the quotient. -/
theorem normRayClassMaximalityClassGroupIsMulCommutative
    (F : Type*) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] normRayClassMaximalityClassGroupIsMulCommutative
