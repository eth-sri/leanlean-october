module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField
public import Mathlib.Tactic.NormNum

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

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

/-- Keep the real-sign quotient normality instance stable across declarations. -/
local instance
    hilbertClassFieldComparison_realSignGroupIsMulCommutative :
    IsMulCommutative (RayClass.realSignGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- On an idele representative, the big-Hilbert quotient equivalence is
the canonical representative in the narrow class group. -/
@[simp]
theorem bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk
    (a : IdeleGroup K) :
    bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K))
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      QuotientGroup.mk'
        (RayClass.narrowDenominator (K := K)) a := by
  rfl

/-- On an idele representative, the small-Hilbert quotient equivalence is
the ordinary ideal-class map. -/
@[simp]
theorem smallHilbertClassFieldQuotientEquivClassGroup_mk
    (a : IdeleGroup K) :
    smallHilbertClassFieldQuotientEquivClassGroup
        (K := K)
        (QuotientGroup.mk'
          (smallHilbertClassFieldNormSubgroup (K := K))
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      IdeleGroup.idealClass a := by
  rfl





/-- The canonical map from real sign classes to the big-Hilbert
reciprocity quotient. -/
def realSignToBigHilbertClassFieldQuotient :
    RayClass.realSignGroup K →*
      (IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K)) :=
  (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).symm.toMonoidHom.comp
    (RayClass.signToNarrow (K := K))

/-- The real-sign map to the big-Hilbert quotient is the composite used in
its definition. -/
@[simp]
theorem realSignToBigHilbertClassFieldQuotient_apply
    (s : RayClass.realSignGroup K) :
    realSignToBigHilbertClassFieldQuotient (K := K) s =
      (bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)).symm
          (RayClass.signToNarrow (K := K) s) :=
  rfl











 

 



 theorem signToNarrow_mem_narrowClassKernel
    (s : RayClass.realSignGroup K) :
    RayClass.signToNarrow (K := K) s ∈
      MonoidHom.ker (RayClass.narrowToClassGroup (K := K)) := by
  rw [←
    RayClass.signToNarrow_range_eq_narrowToClassGroup_ker
      (K := K)]
  norm_num

/-- The real-sign map with codomain restricted to the kernel of the
narrow-to-ordinary class-group map. -/
def realSignToNarrowClassKernel :
    RayClass.realSignGroup K →*
      MonoidHom.ker (RayClass.narrowToClassGroup (K := K)) where
  toFun s :=
    ⟨RayClass.signToNarrow (K := K) s,
      signToNarrow_mem_narrowClassKernel (K := K) s⟩
  map_one' := by
    norm_num
  map_mul' s t := by
    norm_num

/-- The restricted real-sign map has the same underlying narrow ideal class
as `RayClass.signToNarrow`. -/
@[simp]
theorem realSignToNarrowClassKernel_apply
    (s : RayClass.realSignGroup K) :
    (realSignToNarrowClassKernel (K := K) s :
      RayClass.NarrowClassGroup K) =
      RayClass.signToNarrow (K := K) s :=
  rfl











end GlobalClassFields
end GlobalClassFieldTheory

end
