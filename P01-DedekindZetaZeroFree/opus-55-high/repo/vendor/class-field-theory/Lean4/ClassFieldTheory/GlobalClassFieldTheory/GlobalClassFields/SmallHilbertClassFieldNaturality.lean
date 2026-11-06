module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Naturality of the small Hilbert class field

An equivalence of number fields carries the small-Hilbert norm subgroup
exactly onto the small-Hilbert norm subgroup.  Consequently it induces the
canonical equivalence of the corresponding reciprocity quotients.  Transport
of ordinary ideal classes is obtained from this quotient equivalence and is
therefore compatible with the canonical quotient--class-group equivalences.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

/-- Supply the canonical commutativity used by both small-Hilbert quotients. -/
theorem smallHilbertNaturalityIdeleClassIsMulCommutative
    {F : Type*} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) := by apply GlobalClassFieldTheory.GlobalClassFields.hilbertClassFieldComparison_ideleClassGroupIsMulCommutative <;> assumption

attribute [local instance] smallHilbertNaturalityIdeleClassIsMulCommutative
