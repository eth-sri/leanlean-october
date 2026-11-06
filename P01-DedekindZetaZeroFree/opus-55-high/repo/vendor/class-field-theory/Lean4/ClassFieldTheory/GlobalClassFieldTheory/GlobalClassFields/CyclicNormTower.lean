module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Exact norm quotients in a cyclic tower

For a tower of cyclic Galois extensions, the first map in the concrete
idele-class norm-quotient sequence is injective.  Together with the
already available right exactness, this gives the short exact norm
sequence and its exact cardinal factorization.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField
open RelativeIdeleGroup.Cohomology

theorem cyclicNormTower_relativeClassGroupIsMulCommutative
    (A B : Type) [Field A] [NumberField A] [Field B] [Algebra A B] :
    IsMulCommutative (RelativeIdeleGroup.ClassGroup A B) := by apply GlobalClassFieldTheory.ClassFieldAxiom.cyclicNormRelative_isMulCommutative <;> assumption

attribute [local instance] cyclicNormTower_relativeClassGroupIsMulCommutative

theorem cyclicNormTower_ideleClassGroupIsMulCommutative
    (A : Type) [Field A] [NumberField A] :
    IsMulCommutative (IdeleClassGroup A) := by apply normIdeleClassGroup_isMulCommutative <;> assumption

attribute [local instance] cyclicNormTower_ideleClassGroupIsMulCommutative
