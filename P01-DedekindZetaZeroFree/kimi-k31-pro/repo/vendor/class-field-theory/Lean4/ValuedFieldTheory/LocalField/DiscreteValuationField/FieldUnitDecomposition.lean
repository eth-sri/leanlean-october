module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestriction
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.SeriesValuationEstimates
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuationUniformizer
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.UniformizerIntegerValuation
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.LocalFieldRangeRestriction
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuedExtensionUnitMap
public import Mathlib.Topology.Algebra.Group.Units

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/















set_option autoImplicit false

/-!
# Principal-unit decomposition

This file connects the principal-unit decomposition proved in
`PrincipalUnits` to the standard integer-valued field-unit valuation attached
to a `ℤᵐ⁰`-valued complete discrete valuation.
-/

noncomputable section

open Filter
open scoped Topology
open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

variable {K : Type u} [Field K]





/-- The uniformizer–residue–principal-unit decomposition, group-isomorphism form for a complete
DVF with a fixed uniformizer:
`K^* ≃ μ_{q-1} × U^1 × ℤ`. -/
noncomputable def fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    fieldUnitDecompositionFactors F ≃* Kˣ := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F)
        hπ
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  exact
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_zeroSubgroup_eq_unitGroup
      (F := F) V hzero hπV

/--
The defining evaluation formula for `fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF`
is `fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ z =
valuationSubringUnitFieldUnitHom F (z.1.1 : F.valuationSubringˣ) *
valuationSubringUnitFieldUnitHom F (z.1.2 : F.valuationSubringˣ) * (Units.mk0 (π : K) hπ.ne_zero)
^ Multiplicative.toAdd z.2`.
-/
@[simp]
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (z : fieldUnitDecompositionFactors F) :
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
        F hπ z =
      valuationSubringUnitFieldUnitHom F
          (z.1.1 : F.valuationSubringˣ) *
        valuationSubringUnitFieldUnitHom F
          (z.1.2 : F.valuationSubringˣ) *
        (Units.mk0 (π : K) hπ.ne_zero) ^ Multiplicative.toAdd z.2 := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F)
        hπ
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  have happ :=
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply
      F V
      (fun y =>
        mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
          (F := F) V hzero y)
      hπV z
  simp [fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF,
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_zeroSubgroup_eq_unitGroup]

/--
Establishes the identity `((CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ).val
(fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ z) = Multiplicative.toAdd z.2`.
-/
@[simp]
theorem multiplicativeIntegerValuationOfUniformizer_fieldUnitsEquivRootsPrincipalUnitsUniformizer
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (z : fieldUnitDecompositionFactors F) :
    ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ).val
        (fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
          F hπ z) =
      Multiplicative.toAdd z.2 := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          valuationSubringUnitFieldUnitHom F u = y := by
    intro y
    exact
      mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
        (F := F) V
        (by
          simpa [V] using
            (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F) hπ)
        y
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  have hunit :
      valuationSubringUnitFieldUnitHom F
            (z.1.1 : F.valuationSubringˣ) *
          valuationSubringUnitFieldUnitHom F
            (z.1.2 : F.valuationSubringˣ) ∈
        V.zeroSubgroup :=
    (hzero _).2
      ⟨(z.1.1 : F.valuationSubringˣ) * (z.1.2 : F.valuationSubringˣ), by
        rw [map_mul]⟩
  rw [fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply]
  exact V.valuation_uniformizer_normal_form hπV hunit (Multiplicative.toAdd z.2)

/--
Establishes the identity `(CompleteDVF.uniformizerValueExponent F) hπ
(fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ z) = Multiplicative.toAdd z.2`.
-/
@[simp]
theorem uniformizerValueExponent_fieldUnitsEquivRootsPrincipalUnitsUniformizer
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (z : fieldUnitDecompositionFactors F) :
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ
        (fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
          F hπ z) =
      Multiplicative.toAdd z.2 :=
  multiplicativeIntegerValuationOfUniformizer_fieldUnitsEquivRootsPrincipalUnitsUniformizer
    F hπ z

/--
Establishes the identity `Multiplicative.toAdd
((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ).symm x).2 =
(CompleteDVF.uniformizerValueExponent F) hπ x`.
-/
@[simp]
theorem uniformizerValueExponent_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    Multiplicative.toAdd
        ((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
          F hπ).symm x).2 =
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x := by
  have h :=
    uniformizerValueExponent_fieldUnitsEquivRootsPrincipalUnitsUniformizer
      F hπ
      ((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
        F hπ).symm x)
  simpa using h.symm

/--
Establishes the identity `((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F
hπ).symm x).2 = Multiplicative.ofAdd ((CompleteDVF.uniformizerValueExponent F) hπ x)`.
-/
@[simp]
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_snd
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    ((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ).symm x).2 =
      Multiplicative.ofAdd ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x) := by
  let E :=
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ
  have h :
      Multiplicative.toAdd ((E.symm x).2) =
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x := by
    simp [E]
  calc
    (E.symm x).2 = Multiplicative.ofAdd (Multiplicative.toAdd ((E.symm x).2)) := by
      simp
    _ = Multiplicative.ofAdd ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x) := by
      rw [h]





/--
Establishes the membership statement `x * (Units.mk0 (π : K) hπ.ne_zero) ^
(-((CompleteDVF.uniformizerValueExponent F) hπ x)) ∈ F.valuation.valuationSubring.unitGroup`.
-/
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_unitPart_mem_unitGroup
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)) ∈
      F.valuation.valuationSubring.unitGroup := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero :
      V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F) hπ
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  have hmem :
      x * (Units.mk0 (π : K) hπ.ne_zero) ^
          (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)) ∈
        V.zeroSubgroup := by
    rw [V.mem_zeroSubgroup_iff, V.val_mul, V.val_uniformizer_zpow hπV]
    simp [V]
  simpa [hzero] using hmem

/-- The valuation-ring unit obtained by removing the uniformizer power from a
field unit. -/
noncomputable def fieldUnitUniformizerUnitPart
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) : F.valuationSubringˣ :=
  F.valuation.valuationSubring.unitGroupMulEquiv
    ⟨x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)),
      fieldUnitsEquivRootsPrincipalUnitsUniformizer_unitPart_mem_unitGroup
        F hπ x⟩

/--
Establishes the identity `valuationSubringUnitFieldUnitHom F (fieldUnitUniformizerUnitPart F hπ x)
= x * (Units.mk0 (π : K) hπ.ne_zero) ^ (-((CompleteDVF.uniformizerValueExponent F) hπ x))`.
-/
@[simp]
theorem valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    valuationSubringUnitFieldUnitHom F
        (fieldUnitUniformizerUnitPart F hπ x) =
      x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)) := by
  apply Units.ext
  simp [valuationSubringUnitFieldUnitHom, fieldUnitUniformizerUnitPart]















































end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
