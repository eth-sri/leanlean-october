module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ProfiniteUnits
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Topological decomposition of a local multiplicative group

This file packages the normalized valuation and the unit factor in the standard
decomposition of `Kˣ` as continuous homomorphisms. After fixing a
noncanonical uniformizer internally, the resulting parameter-free map lets
downstream separation arguments avoid carrying a uniformizer parameter.
-/

noncomputable section

universe u

namespace LocalFieldTheory.IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero







/-- The unit factor of one is one. -/
@[simp]
theorem uniformizerUnitFactor_one
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    uniformizerUnitFactor K ϖ hϖ 1 = 1 := by
  apply integerUnitsToFieldUnits_injective K
  rw [integerUnitsToFieldUnits_uniformizerUnitFactor]
  rw [valuationMap_ofMul_one]
  simp

/-- The unit factor respects multiplication. -/
theorem uniformizerUnitFactor_mul
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (x y : Kˣ) :
    uniformizerUnitFactor K ϖ hϖ (x * y) =
      uniformizerUnitFactor K ϖ hϖ x * uniformizerUnitFactor K ϖ hϖ y := by
  apply integerUnitsToFieldUnits_injective K
  rw [map_mul]
  simp only [integerUnitsToFieldUnits_uniformizerUnitFactor]
  rw [valuationMap_ofMul_mul, zpow_add]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl







/-- The fixed noncanonical uniformizer used by the parameter-free unit map. -/
def chosenLocalUniformizer
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ :=
  Classical.choose (valuationMap_uniformiser K)

/-- The chosen local uniformizer has normalized valuation one. -/
@[simp]
theorem chosenLocalUniformizer_spec
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    valuationMap K (Additive.ofMul (chosenLocalUniformizer K)) = 1 :=
  Classical.choose_spec (valuationMap_uniformiser K)



end LocalFieldTheory.IsNonarchimedeanLocalField

end
