module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdealClass
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison
public import Mathlib.RingTheory.ClassGroup.ExtendedHom

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# The principal ideal theorem

This file descends genuine idele extension to the reciprocity quotients
defining the two small Hilbert class fields and proves that the resulting
map forms the naturality square with the existing ideal-class extension
`ClassGroup.extendedHom`.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField

/-- Canonical class-group commutativity supplies normality for the quotient. -/
theorem principalIdealTheoremClassGroupIsMulCommutative
    (F : Type*) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] principalIdealTheoremClassGroupIsMulCommutative

section SmallHilbertIdeleExtension

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [IsGalois K L] in
/-- The map on small-Hilbert reciprocity quotients induced by the
concrete extension map on ideles. -/
noncomputable def smallHilbertClassFieldIdeleExtensionMap :
    (IdeleClassGroup K ⧸
        GlobalClassFields.smallHilbertClassFieldNormSubgroup) →*
      (IdeleClassGroup L ⧸
        GlobalClassFields.smallHilbertClassFieldNormSubgroup) :=
  QuotientGroup.map
    GlobalClassFields.smallHilbertClassFieldNormSubgroup
    GlobalClassFields.smallHilbertClassFieldNormSubgroup
    (ideleClassExtension K L)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change
        ideleClassExtension K L
            (QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K) a) ∈
          GlobalClassFields.smallHilbertClassFieldNormSubgroup
      rw [ideleClassExtension_mk]
      exact
        ⟨IdeleGroup.extension K L a,
          IdeleGroup.extension_mem_ordinaryIdealClassSubgroup
            K L ha,
          rfl⟩)

omit [IsGalois K L] in
/-- Evaluation of the small-Hilbert idele-extension map on a quotient
representative. -/
@[simp]
theorem smallHilbertClassFieldIdeleExtensionMap_mk'
    (c : IdeleClassGroup K) :
    smallHilbertClassFieldIdeleExtensionMap K L
        (QuotientGroup.mk'
          (GlobalClassFields.smallHilbertClassFieldNormSubgroup (K := K)) c) =
      QuotientGroup.mk'
        (GlobalClassFields.smallHilbertClassFieldNormSubgroup (K := L))
        (ideleClassExtension K L c) := by
  rfl



end SmallHilbertIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory

end
