module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Quotients
public import Mathlib.Data.Int.ModEq

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Integer value-group images

This file contains the integer value-group subgroup-image lemmas used by the norm and ramification-image arguments.  The results are purely about
integer-valued multiplicative valuations and integer lcm divisibility.
-/

noncomputable section

namespace DiscreteValuationField











namespace MultiplicativeIntegerValuation

variable {G : Type _} [Group G]

/-- The subgroup of valuation values attained by elements of a subgroup of the
valued group. -/
def subgroupValueSubgroup
    (V : MultiplicativeIntegerValuation G) (S : Subgroup G) :
    Subgroup (Multiplicative ℤ) where
  carrier := {n | ∃ x : G, x ∈ S ∧ V.valuationHom x = n}
  one_mem' := ⟨1, S.one_mem, V.valuationHom.map_one⟩
  mul_mem' := by
    rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, S.mul_mem hx hy, V.valuationHom.map_mul x y⟩
  inv_mem' := by
    rintro a ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, S.inv_mem hx, V.valuationHom.map_inv x⟩

/--
Characterizes `n ∈ V.subgroupValueSubgroup S` by the equivalent condition `∃ x : G, x ∈ S ∧
V.valuationHom x = n`.
-/
@[simp] theorem mem_subgroupValueSubgroup_iff
    (V : MultiplicativeIntegerValuation G) (S : Subgroup G)
    (n : Multiplicative ℤ) :
    n ∈ V.subgroupValueSubgroup S ↔
      ∃ x : G, x ∈ S ∧ V.valuationHom x = n :=
  Iff.rfl















end MultiplicativeIntegerValuation

end DiscreteValuationField

end

end LocalFieldTheory
