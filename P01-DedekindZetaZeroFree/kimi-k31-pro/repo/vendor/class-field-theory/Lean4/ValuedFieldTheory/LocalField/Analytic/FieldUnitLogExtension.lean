module

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

/-- Extend a homomorphism on first principal units to the three factors in
the uniformizer–residue–principal-unit decomposition, killing the residue-root factor and assigning the additive
value `c` to one power of the chosen uniformizer. -/
noncomputable def fieldUnitDecompositionLogHomWithUniformizerValue
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A) :
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
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (z : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F) :
    fieldUnitDecompositionLogHomWithUniformizerValue F φ c z =
      φ z.1.2 * Multiplicative.ofAdd (Multiplicative.toAdd z.2 • c) :=
  rfl

/--
Establishes the identity `fieldUnitDecompositionLogHomWithUniformizerValue F φ c ((ζ, 1), (1 :
Multiplicative ℤ)) = 1`.
-/
@[simp] theorem fieldUnitDecompositionLogHomWithUniformizerValue_root
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (ζ : CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
    fieldUnitDecompositionLogHomWithUniformizerValue F φ c
        ((ζ, 1), (1 : Multiplicative ℤ)) = 1 := by
  simp

/--
Establishes the identity `fieldUnitDecompositionLogHomWithUniformizerValue F φ c (((1 :
CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), u), (1 : Multiplicative ℤ)) = φ
u`.
-/
@[simp] theorem fieldUnitDecompositionLogHomWithUniformizerValue_principal
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    fieldUnitDecompositionLogHomWithUniformizerValue F φ c
        (((1 : CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), u),
          (1 : Multiplicative ℤ)) = φ u := by
  simp

/--
Establishes the identity `fieldUnitDecompositionLogHomWithUniformizerValue F φ c (((1 :
CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), (1 :
(CompleteDVF.higherPrincipalUnitGroup F) 1)), Multiplicative.ofAdd m) = Multiplicative.ofAdd (m •
c)`.
-/
@[simp] theorem fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (m : ℤ) :
    fieldUnitDecompositionLogHomWithUniformizerValue F φ c
        (((1 : CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F),
            (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)),
          Multiplicative.ofAdd m) = Multiplicative.ofAdd (m • c) := by
  simp

/-- Transport the corrected factor logarithm across a chosen the uniformizer–residue–principal-unit decomposition
decomposition of the field-unit group. -/
noncomputable def fieldUnitLogHomWithUniformizerValue
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (d : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A) :
    Kˣ →* Multiplicative A :=
  (fieldUnitDecompositionLogHomWithUniformizerValue F φ c).comp
    d.symm.toMonoidHom

/--
The defining evaluation formula for `fieldUnitLogHomWithUniformizerValue` is
`fieldUnitLogHomWithUniformizerValue F d φ c x = φ (d.symm x).1.2 * Multiplicative.ofAdd
(Multiplicative.toAdd (d.symm x).2 • c)`.
-/
@[simp] theorem fieldUnitLogHomWithUniformizerValue_apply
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (d : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A) (x : Kˣ) :
    fieldUnitLogHomWithUniformizerValue F d φ c x =
      φ (d.symm x).1.2 *
        Multiplicative.ofAdd (Multiplicative.toAdd (d.symm x).2 • c) :=
  rfl















end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
