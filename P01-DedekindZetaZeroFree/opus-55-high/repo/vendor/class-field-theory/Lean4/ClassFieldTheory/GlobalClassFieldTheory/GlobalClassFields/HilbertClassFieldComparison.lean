module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Comparison of the big and small Hilbert class fields

This file identifies the canonical transition from the big-Hilbert
reciprocity quotient to the small-Hilbert reciprocity quotient with the
canonical map from the narrow class group to the ordinary class group.
It then transports the archimedean sign exact sequence to a precise
description of the kernel of that transition.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Fix the canonical commutativity needed for Hilbert norm-subgroup
quotients in this module. -/
theorem hilbertClassFieldComparison_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] hilbertClassFieldComparison_ideleClassGroupIsMulCommutative
