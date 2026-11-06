module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import Mathlib.Data.Finsupp.Order

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Projection between ray class groups

The idèle-class quotient gives the canonical map from a larger ray modulus
to a smaller one. The public ray-class groups use the comparison equivalence
to transport this map.
-/

open scoped NumberField Classical

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K]

local instance ideleClassIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance rayCongruenceNormal (m : RayClass.Modulus K) :
    (RayClass.Modulus.congruenceSubgroup m).Normal :=
  Subgroup.normal_of_isMulCommutative _















end ClassFieldTheory

end
