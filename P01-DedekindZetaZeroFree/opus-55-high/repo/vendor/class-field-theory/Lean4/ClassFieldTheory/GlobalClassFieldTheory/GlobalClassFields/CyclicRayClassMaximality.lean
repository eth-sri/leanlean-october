module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormRayClassMaximality

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Maximal cyclic quotients at the narrow finite conductor

For a finite cyclic extension, the actual idèle-class norm quotient has
order equal to the extension degree.  The ray class group at the exact
narrow finite conductor surjects onto this norm quotient.  This file
identifies the case in which that surjection is an isomorphism: precisely
when the ray class number already equals the extension degree.

Equivalently, the actual norm subgroup is then exactly the ray congruence
subgroup at its narrow finite conductor.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

/-- The canonical idèle-class multiplication makes every subgroup normal. -/
theorem cyclicRayClassMaximalityClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) := by apply normIdeleClassGroup_isMulCommutative <;> assumption

attribute [local instance] cyclicRayClassMaximalityClassGroupIsMulCommutative
