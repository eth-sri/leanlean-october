module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.CyclicRayClassMaximality
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealArtinQuotient
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Core
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.UnramifiedPrimeArtin
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ProductFormula

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


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
    IsMulCommutative (IdeleClassGroup F) := by apply normIdeleClassGroup_isMulCommutative <;> assumption

attribute [local instance] unramifiedPrimeNormClassGroupIsMulCommutative
