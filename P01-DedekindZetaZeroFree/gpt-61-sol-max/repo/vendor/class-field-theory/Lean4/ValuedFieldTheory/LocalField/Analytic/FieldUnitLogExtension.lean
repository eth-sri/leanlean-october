module

public import Mathlib

public import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.Homomorphisms

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Extending the logarithm to the field-unit group

The logarithm on first principal units does not extend by killing a chosen
uniformizer.  Its uniformizer value must instead be chosen so that the
distinguished rational prime has logarithm zero.  This file isolates that
algebraic construction.
-/

noncomputable section

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

section
variable (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
include F A φ c
/-- Extend a homomorphism on first principal units to the three factors in
the uniformizer–residue–principal-unit decomposition, killing the residue-root factor and assigning the additive
value `c` to one power of the chosen uniformizer. -/
noncomputable def fieldUnitDecompositionLogHomWithUniformizerValue
      :
    CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F →*
      Multiplicative A where
  toFun z :=
    φ z.1.2 * Multiplicative.ofAdd (Multiplicative.toAdd z.2 • c)
  map_one' := by simp
  map_mul' z w := by
    apply Multiplicative.toAdd.injective
    change
      Multiplicative.toAdd (φ (z.1.2 * w.1.2)) +
          (Multiplicative.toAdd z.2 + Multiplicative.toAdd w.2) • c =
        (Multiplicative.toAdd (φ z.1.2) + Multiplicative.toAdd z.2 • c) +
          (Multiplicative.toAdd (φ w.1.2) + Multiplicative.toAdd w.2 • c)
    rw [φ.map_mul]
    simp only [toAdd_mul, add_zsmul]
    abel

/--
The defining evaluation formula for `fieldUnitDecompositionLogHomWithUniformizerValue` is
`fieldUnitDecompositionLogHomWithUniformizerValue F φ c z = φ z.1.2 * Multiplicative.ofAdd
(Multiplicative.toAdd z.2 • c)`.
-/
@[simp] theorem fieldUnitDecompositionLogHomWithUniformizerValue_apply
     
    (z : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F) :
    fieldUnitDecompositionLogHomWithUniformizerValue F φ c z =
      φ z.1.2 * Multiplicative.ofAdd (Multiplicative.toAdd z.2 • c) :=
  rfl
end















































section
variable (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (d : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
include F A d φ c
/-- Transport the corrected factor logarithm across a chosen the uniformizer–residue–principal-unit decomposition
decomposition of the field-unit group. -/
noncomputable def fieldUnitLogHomWithUniformizerValue
       :=
  (fieldUnitDecompositionLogHomWithUniformizerValue F φ c).comp
    d.symm.toMonoidHom

/--
The defining evaluation formula for `fieldUnitLogHomWithUniformizerValue` is
`fieldUnitLogHomWithUniformizerValue F d φ c x = φ (d.symm x).1.2 * Multiplicative.ofAdd
(Multiplicative.toAdd (d.symm x).2 • c)`.
-/
@[simp] theorem fieldUnitLogHomWithUniformizerValue_apply
      (x : Kˣ) :
    fieldUnitLogHomWithUniformizerValue F d φ c x =
      φ (d.symm x).1.2 *
        Multiplicative.ofAdd (Multiplicative.toAdd (d.symm x).2 • c) :=
  rfl
end
































































































































end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
