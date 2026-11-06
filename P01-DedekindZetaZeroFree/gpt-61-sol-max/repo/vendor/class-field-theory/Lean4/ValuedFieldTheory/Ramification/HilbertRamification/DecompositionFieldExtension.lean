module

public import Mathlib

public import ValuedFieldTheory.Ramification.HilbertRamification.DecompositionField

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Decomposition-field extension comparison

This file starts with clause (i): the restriction of `w` to its decomposition
field has a unique extension back to `L`.  The proof works for finite or
infinite Galois extensions and for archimedean or nonarchimedean valuations.
-/

noncomputable section

universe u v

namespace AlgebraicNumberTheory
namespace Valuations

section
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (E : IntermediateField K L)
include K L w E
/-- Restriction of an absolute value on `L` to an intermediate field. -/
def absoluteValueRestrictIntermediateField
       :=
  w.comp (f := algebraMap E L) (algebraMap E L).injective

@[simp] theorem absoluteValueRestrictIntermediateField_apply
      (x : E) :
    absoluteValueRestrictIntermediateField w E x = w x :=
  rfl
end







































































end Valuations
end AlgebraicNumberTheory

end
