module

public import Mathlib.NumberTheory.LocalField.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-!
# Basic structure of nonarchimedean local fields

Compactness facts and the normalized integer-valued valuation attached to a
nonarchimedean local field.
-/


namespace LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- The normalized integer valuation attached to a nonarchimedean local field.

It is obtained by transporting the value group to `WithZero (Multiplicative Int)` and then taking
the exponent of the nonzero value of a field unit. -/
def v (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Additive Kˣ → Int :=
  fun x =>
    Multiplicative.toAdd
      (WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K ((Additive.toMul x : Kˣ) : K)))
        (by simp))

/-- The normalized integer valuation is obtained by transporting the field valuation to
multiplicative integers and taking its additive exponent. -/
@[simp]
theorem v_apply (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Additive Kˣ) :
    v K x =
      Multiplicative.toAdd
        (WithZero.unzero
          (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
            (ValuativeRel.valuation K ((Additive.toMul x : Kˣ) : K)))
          (by simp)) :=
  rfl

/-- Every integer occurs as the normalized valuation of a nonzero field element. -/
theorem v_surjective (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Surjective (v K) := by
  intro n
  let γ : ValuativeRel.ValueGroupWithZero K :=
    (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm
      ((Multiplicative.ofAdd n : Multiplicative Int) : WithZero (Multiplicative Int))
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective γ
  have hγ_ne : γ ≠ 0 := by
    dsimp [γ]
    simp
  have ha0 : a ≠ 0 := by
    intro h
    simp_all
  refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
  simp [v, γ, ha]

/-- The normalized valuation turns multiplication of field units into addition of integers. -/
theorem v_mul (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    v K (Additive.ofMul (x * y)) =
      v K (Additive.ofMul x) + v K (Additive.ofMul y) := by
  simp [v, Valuation.map_mul, WithZero.unzero_mul, toAdd_mul]

/-- The normalized valuation of the multiplicative identity is zero. -/
@[simp]
theorem v_one (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    v K (Additive.ofMul (1 : Kˣ)) = 0 := by
  dsimp [v]
  have hunzero :
      WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K (((1 : Kˣ) : K))))
        (by simp) = (1 : Multiplicative Int) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero]
    simp
  rw [hunzero]
  exact toAdd_one

/-- The normalized valuation of an inverse is the negative of the original valuation. -/
theorem v_inv (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) :
    v K (Additive.ofMul x⁻¹) = -v K (Additive.ofMul x) := by
  have hmul := v_mul K x x⁻¹
  rw [mul_inv_cancel, v_one] at hmul
  omega

/-- The normalized valuation of a quotient is the difference of the two valuations. -/
theorem v_div (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    v K (Additive.ofMul (x / y)) =
      v K (Additive.ofMul x) - v K (Additive.ofMul y) := by
  rw [div_eq_mul_inv, v_mul, v_inv, sub_eq_add_neg]

/-- Raising a field unit to a natural power multiplies its normalized valuation by that power. -/
theorem v_pow (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Nat) :
    v K (Additive.ofMul (x ^ n)) = (n : Int) * v K (Additive.ofMul x) := by
  induction n with
  | zero =>
      rw [pow_zero, v_one]
      simp
  | succ n ih =>
      rw [pow_succ, v_mul, ih]
      rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 by simp]
      ring

/-- Raising a field unit to an integral power multiplies its normalized valuation by that integer.
Raising a field unit to an integral power multiplies its normalized valuation by that integer. -/
theorem v_zpow (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Int) :
    v K (Additive.ofMul (x ^ n)) = n * v K (Additive.ofMul x) := by
  cases n with
  | ofNat n =>
      simpa using v_pow K x n
  | negSucc n =>
      rw [zpow_negSucc, v_inv, v_pow]
      change -(((n + 1 : Nat) : Int) * v K (Additive.ofMul x)) =
        (-(((n + 1 : Nat) : Int))) * v K (Additive.ofMul x)
      ring

/-- The canonical inclusion of valuation-integer units into field units. -/
def integerUnitsToFieldUnits (K : Type u) [Field K] [ValuativeRel K] : 𝒪[K]ˣ →* Kˣ :=
  Units.map (algebraMap 𝒪[K] K).toMonoidHom

/-- The inclusion of valuation-ring units into field units preserves the underlying field element.
The inclusion of valuation-ring units into field units preserves the underlying field element. -/
@[simp]
theorem integerUnitsToFieldUnits_apply (K : Type u) [Field K] [ValuativeRel K]
    (x : 𝒪[K]ˣ) :
    ((integerUnitsToFieldUnits K x : Kˣ) : K) = (((x : 𝒪[K]ˣ) : 𝒪[K]) : K) :=
  rfl

/-- The canonical inclusion of valuation-integer units into field units is
injective. -/
theorem integerUnitsToFieldUnits_injective
    (K : Type u) [Field K] [ValuativeRel K] :
    Function.Injective (integerUnitsToFieldUnits K) := by
  intro x y hxy
  apply Units.ext
  apply Subtype.ext
  simpa [integerUnitsToFieldUnits] using congrArg Units.val hxy

/-- A valuation-integer unit has normalized valuation zero as a field unit. -/
@[simp]
theorem v_integerUnitsToFieldUnits (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : 𝒪[K]ˣ) :
    v K (Additive.ofMul (integerUnitsToFieldUnits K x)) = 0 := by
  have hxv :
      ValuativeRel.valuation K ((integerUnitsToFieldUnits K x : Kˣ) : K) = 1 := by
    simpa [integerUnitsToFieldUnits] using
      (Valuation.Integers.valuation_unit
        (Valuation.integer.integers (ValuativeRel.valuation K)) x)
  rw [v_apply]
  apply (WithZero.toAdd_unzero_eq_iff _ 0).2
  simp_all
