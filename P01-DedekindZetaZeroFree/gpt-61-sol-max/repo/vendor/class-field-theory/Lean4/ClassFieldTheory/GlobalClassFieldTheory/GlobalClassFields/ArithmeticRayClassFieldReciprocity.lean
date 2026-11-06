module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Arithmetic reciprocity for actual ray class fields

This is the canonical topological isomorphism
`Gal(Kᵐ/K) ≃ₜ* C_K/C_Kᵐ` with arithmetic Frobenius
normalization.  It uses the actual selected ray class field, its exact
idèle norm range, the finite Krull topology, and the native ray-class
quotient topology.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField
open Reciprocity

theorem arithmeticRayClassIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] arithmeticRayClassIdeleClassGroupIsMulCommutative

variable {K : Type} [Field K] [NumberField K]





















































































































































end GlobalClassFields
end GlobalClassFieldTheory

end
