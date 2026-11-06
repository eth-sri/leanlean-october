module

public import Mathlib

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

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/













set_option autoImplicit false

/-!
# The direct topology of a standard multiplicative integer valuation

This file transfers completeness from the actual-range restriction of a
complete discrete valuation back to the topology obtained directly from
`Valued.mk' v`.
-/

noncomputable section

universe u

open Filter
open scoped Valued
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace WithZeroValuationTopology

variable {K : Type u} [Field K]

section
variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete v]
include v
/-- The complete-DVF package attached to a standard `ℤᵐ⁰`-valued complete
discrete valuation. -/
def completeDVF
      : CompleteDVF.{u, 0} K where
  ValueGroup := WithZero (Multiplicative ℤ)
  valuation := v
  instCompleteDiscrete := inferInstance

/-- Restricting a standard `ℤᵐ⁰`-valued valuation to its actual range does not
change the uniform structure on the field. -/
theorem valuedMk_uniformSpace_eq_mrangeRestrict
      :
    (Valued.mk' v).toUniformSpace =
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued (completeDVF v)).toUniformSpace := by
  let w :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
      (completeDVF v)
  have hequiv : v.IsEquiv w := by
    intro x y
    rw [← Subtype.coe_le_coe]
    rfl
  change (Valued.mk' v).toUniformSpace = (Valued.mk' w).toUniformSpace
  apply le_antisymm
  · rw [le_iff_uniformContinuous_id]
    exact hequiv.symm.uniformContinuous
  · rw [le_iff_uniformContinuous_id]
    exact hequiv.uniformContinuous

/-- A standard complete discrete valuation with finite residue field makes the
field complete for the topology obtained directly from `Valued.mk' v`. -/
theorem completeSpace_ofWithZeroValuation
     
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    CompleteSpace K := by
  let F  := completeDVF v
  let direct  := Valued.mk' v
  let restrictedNormed  :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F
  have : Finite F.residueField := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance
  have hcomplete : @CompleteSpace K restrictedNormed.toUniformSpace := _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_completeSpace_of_residueField_finite F
  have huniform : direct.toUniformSpace = restrictedNormed.toUniformSpace := by
    change
      (Valued.mk' v).toUniformSpace =
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField
          (completeDVF v)).toUniformSpace
    calc
      (Valued.mk' v).toUniformSpace =
          (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
            (completeDVF v)).toUniformSpace :=
        valuedMk_uniformSpace_eq_mrangeRestrict v
      _ =
          (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField
            (completeDVF v)).toUniformSpace := rfl
  let  := direct
  change @CompleteSpace K direct.toUniformSpace
  rw [huniform]
  exact hcomplete
end


end WithZeroValuationTopology
end LocalFieldTheory.DiscreteValuationField

end
