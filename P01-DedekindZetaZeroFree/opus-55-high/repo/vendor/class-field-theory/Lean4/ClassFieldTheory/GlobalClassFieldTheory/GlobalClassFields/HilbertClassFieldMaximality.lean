module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassField
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.InfinitePlaceTensorNorm
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Maximality criteria for Hilbert class fields

An unramified cyclic extension reaches the big or small Hilbert norm
subgroup exactly when its degree reaches the corresponding narrow or
ordinary class number.  Thus a maximal-degree unramified cyclic
extension has the canonical Hilbert reciprocity quotient.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

theorem hilbertClassFieldMaximalityIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) := by apply normIdeleClassGroup_isMulCommutative <;> assumption

attribute [local instance] hilbertClassFieldMaximalityIdeleClassGroupIsMulCommutative
