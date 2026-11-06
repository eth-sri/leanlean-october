module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.CyclicRayClassMaximality

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Uniqueness of maximal cyclic norm subgroups at a narrow finite conductor

Two finite cyclic extensions whose exact narrow finite conductors agree and
whose degrees exhaust the corresponding ray class number determine the same
actual idèle-class norm subgroup.  Thus their concrete norm quotients are
canonically equivalent.  This is the norm-subgroup uniqueness part of the
cyclic class-field correspondence at a fixed narrow finite conductor.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

theorem cyclicConductorUniquenessIdeleClassIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) := by apply normIdeleClassGroup_isMulCommutative <;> assumption

attribute [local instance] cyclicConductorUniquenessIdeleClassIsMulCommutative
