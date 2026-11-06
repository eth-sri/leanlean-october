module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorFrobenius
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FinitePlaceArtinQuotient
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.UnramifiedPrimeArtin
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ProductFormula

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Prime norm classes at unramified finite places

For a finite abelian extension of number fields, the normalized
order-one element at a finite place defines a class in the chosen
local norm quotient.  Under local reciprocity this class is the actual
prime Artin element in the chosen decomposition group.

At a chosen unramified place, its order is therefore the local degree,
and its triviality is equivalent to complete splitting.  The
one-place local-to-global norm map sends this local class to the
corresponding prime class in the global idèle-class norm quotient, so
the order of the global class divides the local degree.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

theorem unramifiedPrimeNormClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] unramifiedPrimeNormClassGroupIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section FiniteGalois

variable [IsGalois K L]




































end FiniteGalois

variable [IsAbelianGalois K L]



























































































































































end GlobalClassFields
end GlobalClassFieldTheory

end
