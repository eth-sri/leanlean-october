module

public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Narrow ideal classes

This file proves the exact sequence from
global unit signs through the narrow and ordinary class groups.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

theorem finiteCongruenceSubgroup_zero :
    finiteCongruenceSubgroup (0 : FiniteModulus K) =
      FiniteIdeleGroup.integralSubgroup (K := K) := by
  ext a
  simp only [mem_finiteCongruenceSubgroup_iff,
    Finsupp.zero_apply, localHigherUnitGroup_zero,
    FiniteIdeleGroup.mem_integralSubgroup_iff]
