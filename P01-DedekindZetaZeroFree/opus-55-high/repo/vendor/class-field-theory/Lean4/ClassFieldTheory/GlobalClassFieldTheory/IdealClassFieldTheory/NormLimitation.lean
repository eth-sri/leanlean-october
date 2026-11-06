module

public import ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.FieldTheory.Galois.Abelian
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormalClosureNorm
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueAbelianizationNaturality
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormTowerConductor
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealArtinMap

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Ideal and ray consequences of norm limitation

For a finite extension `L / K`, norm limitation identifies its idèle-class
norm range with that of the maximal abelian subfield in the chosen finite
normal closure.  This leaf transports that equality to the corresponding
ideal norm group for every defining modulus and to the image of the norm
range in every ray class group.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

theorem normLimitationIdeleClassIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) := by apply normIdeleClassGroup_isMulCommutative <;> assumption

attribute [local instance] normLimitationIdeleClassIsMulCommutative
