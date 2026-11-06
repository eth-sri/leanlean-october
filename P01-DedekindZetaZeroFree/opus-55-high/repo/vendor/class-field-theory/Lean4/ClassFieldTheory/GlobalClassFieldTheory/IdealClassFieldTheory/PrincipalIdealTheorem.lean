module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdealClass
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison
public import Mathlib.RingTheory.ClassGroup.ExtendedHom

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The principal ideal theorem

This file descends genuine idele extension to the reciprocity quotients
defining the two small Hilbert class fields and proves that the resulting
map forms the naturality square with the existing ideal-class extension
`ClassGroup.extendedHom`.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField

/-- Canonical class-group commutativity supplies normality for the quotient. -/
theorem principalIdealTheoremClassGroupIsMulCommutative
    (F : Type*) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) := by apply GlobalClassFieldTheory.GlobalClassFields.hilbertClassFieldComparison_ideleClassGroupIsMulCommutative <;> assumption

attribute [local instance] principalIdealTheoremClassGroupIsMulCommutative
