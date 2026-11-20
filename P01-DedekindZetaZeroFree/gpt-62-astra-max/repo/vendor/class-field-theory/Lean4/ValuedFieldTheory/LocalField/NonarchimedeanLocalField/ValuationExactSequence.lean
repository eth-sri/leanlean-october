module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false
/-!
# The valuation exact sequence

Builds the normalized valuation map `Kˣ → ℤ` and proves exactness of the
sequence from valuation-ring units through field units to `ℤ`.
-/

namespace LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

section

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The multiplicative normalized valuation on field units. -/
noncomputable def valuationUnitsMulHom : Kˣ →* Multiplicative Int :=
  (@WithZero.unitsWithZeroEquiv (Multiplicative Int) _).toMonoidHom.comp
    ((Units.map (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidHom).comp
      (Units.map (ValuativeRel.valuation K).toMonoidWithZeroHom.toMonoidHom))

/-- The actual normalized valuation map on field units, bundled as an additive hom. -/
noncomputable def valuationMap : Additive Kˣ →+ Int :=
  MonoidHom.toAdditive (valuationUnitsMulHom K)

/-- The additive valuation map evaluates a field unit by applying the normalized integer valuation.
The additive valuation map evaluates a field unit by applying the normalized integer valuation. -/
@[simp]
theorem valuationMap_apply (x : Additive Kˣ) :
    valuationMap K x = v K x :=
  rfl

/-- Every integer is the valuation of some field unit. -/
theorem valuationMap_surjective :
    Function.Surjective (valuationMap K) :=
  v_surjective K

/-- A valuation-theoretic uniformizer, regarded as a unit of the ambient
field.  The nonzero proof is supplied by the actual uniformizer property. -/
noncomputable def uniformizerFieldUnit
    (π : 𝒪[K])
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K)) :
    Kˣ :=
  Units.mk0 (π : K) hπ.ne_zero

/-- Coercing the field unit attached to a valuation-theoretic uniformizer
recovers the original field element. -/
@[simp]
theorem uniformizerFieldUnit_coe
    (π : 𝒪[K])
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K)) :
    (uniformizerFieldUnit K π hπ : K) = (π : K) :=
  rfl

/-- A valuation-theoretic uniformizer has normalized additive value `-1`
in the inverse-standard convention used by the concrete local Artin map. -/
theorem valuationMap_uniformizerFieldUnit
    (π : 𝒪[K])
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K)) :
    valuationMap K
        (Additive.ofMul (uniformizerFieldUnit K π hπ)) =
      -1 := by
  simpa using
    (v_integerRingIrreducibleFieldUnit K π ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).2
      (Valuation.IsUniformizer.is_generator
         hπ))
      (uniformizerFieldUnit K π hπ) rfl)

/-- The additive valuation map sends the zero element of the additive unit group to zero. -/
@[simp]
theorem valuationMap_zero :
    valuationMap K (0 : Additive Kˣ) = 0 :=
  map_zero (valuationMap K)

/-- The multiplicative identity, viewed additively, has valuation zero. -/
@[simp]
theorem valuationMap_ofMul_one :
    valuationMap K (Additive.ofMul (1 : Kˣ)) = 0 := by
  exact valuationMap_zero K

/-- The valuation of a product of field units is the sum of their valuations. -/
theorem valuationMap_ofMul_mul (x y : Kˣ) :
    valuationMap K (Additive.ofMul (x * y)) =
      valuationMap K (Additive.ofMul x) + valuationMap K (Additive.ofMul y) := by
  exact v_mul K x y

/-- The valuation of an inverse field unit is the negative of its valuation. -/
theorem valuationMap_ofMul_inv (x : Kˣ) :
    valuationMap K (Additive.ofMul x⁻¹) =
      -valuationMap K (Additive.ofMul x) := by
  exact v_inv K x

/-- A field unit with additive valuation zero has multiplicative valuation one. -/
theorem valuation_eq_one_of_valuationMap_eq_zero
    {x : Kˣ} (hx : valuationMap K (Additive.ofMul x) = 0) :
    ValuativeRel.valuation K (x : K) = 1 := by
  rw [valuationMap_apply] at hx
  dsimp [v] at hx
  have hunzero :
      WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K) (ValuativeRel.valuation K (x : K)))
        (by simp) = (1 : Multiplicative Int) := by
    exact (congrArg Multiplicative.ofAdd hx)
  apply (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
  have hcoe :
      ((WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K) (ValuativeRel.valuation K (x : K)))
        (by simp) : Multiplicative Int) : WithZero (Multiplicative Int)) =
        (1 : WithZero (Multiplicative Int)) := by
    simpa using congrArg
      (fun y : Multiplicative Int => (y : WithZero (Multiplicative Int))) hunzero
  simp at hcoe
  simpa using hcoe

/-- The valuation of a quotient of field units is the difference of their valuations. -/
theorem valuationMap_ofMul_div (x y : Kˣ) :
    valuationMap K (Additive.ofMul (x / y)) =
      valuationMap K (Additive.ofMul x) - valuationMap K (Additive.ofMul y) := by
  exact v_div K x y

/-- The valuation of an integral power is the exponent times the original valuation. -/
theorem valuationMap_ofMul_zpow (x : Kˣ) (n : Int) :
    valuationMap K (Additive.ofMul (x ^ n)) =
      n * valuationMap K (Additive.ofMul x) := by
  apply v_zpow

/-- The valuation of a natural power is the power times the original valuation. -/
theorem valuationMap_ofMul_pow (x : Kˣ) (n : Nat) :
    valuationMap K (Additive.ofMul (x ^ n)) =
      (n : Int) * valuationMap K (Additive.ofMul x) := by
  exact v_pow K x n

end

section

variable (K : Type u) [Field K] [ValuativeRel K]

/-- Defines `additiveIntegerUnitsToFieldUnits`. -/
def additiveIntegerUnitsToFieldUnits :
    Additive 𝒪[K]ˣ →+ Additive Kˣ :=
  MonoidHom.toAdditive (integerUnitsToFieldUnits K)

/-- The additive inclusion of valuation-ring units agrees with the underlying multiplicative
inclusion. -/
@[simp]
theorem additiveIntegerUnitsToFieldUnits_apply
    (u : 𝒪[K]ˣ) :
    additiveIntegerUnitsToFieldUnits K (Additive.ofMul u) =
      Additive.ofMul (integerUnitsToFieldUnits K u) :=
  rfl

end

section

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Defines `integerUnitOfValuationMapZero`. -/
def integerUnitOfValuationMapZero
    (x : Kˣ) (hx : valuationMap K (Additive.ofMul x) = 0) : 𝒪[K]ˣ where
  val := ⟨(x : K), by
    rw [valuation_integer_membership]
    have hv := valuation_eq_one_of_valuationMap_eq_zero K hx
    simp [hv]⟩
  inv := ⟨(x⁻¹ : K), by
    rw [valuation_integer_membership]
    have hv := valuation_eq_one_of_valuationMap_eq_zero K hx
    simp [hv]⟩
  val_inv := by
    ext
    simp
  inv_val := by
    ext
    simp

/-- The valuation-ring unit reconstructed from a field unit of valuation zero maps back to that
field unit. -/
@[simp]
theorem integerUnitOfValuationMapZero_spec
    (x : Kˣ) (hx : valuationMap K (Additive.ofMul x) = 0) :
    integerUnitsToFieldUnits K (integerUnitOfValuationMapZero K x hx) = x := by
  ext
  rfl

/-- A field unit comes from a valuation-ring unit exactly when its additive valuation is zero. -/
theorem integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero
    (x : Kˣ) :
    x ∈ MonoidHom.range (integerUnitsToFieldUnits K) ↔
      valuationMap K (Additive.ofMul x) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [valuationMap_apply]
    exact v_integerUnitsToFieldUnits K u
  · solve_by_elim [integerUnitOfValuationMapZero, integerUnitOfValuationMapZero_spec]

/-- A valuation-integer unit is an `n`-th power among integer units exactly
when it is an `n`-th power among field units. -/
theorem mem_powMonoidHom_range_integerUnits_iff
    (n : ℕ+) (x : 𝒪[K]ˣ) :
    x ∈ (powMonoidHom (n : ℕ) : 𝒪[K]ˣ →* 𝒪[K]ˣ).range ↔
      integerUnitsToFieldUnits K x ∈
        (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ :=
      (MonoidHom.mem_range
        ).mp hx
    simp at hy
    apply
      (MonoidHom.mem_range
        ).mpr
    refine ⟨integerUnitsToFieldUnits K y, ?_⟩
    rw [powMonoidHom_apply, ← map_pow, hy]
  · intro hx
    obtain ⟨y, hy⟩ :=
      (MonoidHom.mem_range
        ).mp hx
    simp at hy
    have hyValPow :
        valuationMap K (Additive.ofMul (y ^ (n : ℕ))) = 0 := by
      rw [hy, valuationMap_apply]
      exact v_integerUnitsToFieldUnits K x
    rw [valuationMap_ofMul_pow] at hyValPow
    apply
      (MonoidHom.mem_range
        ).mpr
    refine ⟨(integerUnitOfValuationMapZero K y ((mul_eq_zero.mp hyValPow).resolve_left
      (Int.ofNat_ne_zero.mpr n.ne_zero))), ?_⟩
    apply integerUnitsToFieldUnits_injective K
    rw [powMonoidHom_apply, map_pow,
      integerUnitOfValuationMapZero_spec, hy]

/-- The quotient of a field unit by the corresponding power of a uniformizer has
normalized valuation zero. -/
theorem uniformizerUnitFactorValuationZero
    (ϖ x : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    valuationMap K
      (Additive.ofMul (x / ϖ ^ valuationMap K (Additive.ofMul x))) = 0 := by
  rw [valuationMap_ofMul_div, valuationMap_ofMul_zpow, hϖ, mul_one, sub_self]

end

/-- The integer-unit factor in the standard decomposition `x = u * ϖ ^ v(x)`. -/
noncomputable def uniformizerUnitFactor (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (x : Kˣ) : 𝒪[K]ˣ :=
  integerUnitOfValuationMapZero K
    (x / ϖ ^ valuationMap K (Additive.ofMul x))
    (uniformizerUnitFactorValuationZero K ϖ x hϖ)

/-- Removing the uniformizer power prescribed by a field unit's valuation leaves a valuation-ring
unit. -/
@[simp]
theorem integerUnitsToFieldUnits_uniformizerUnitFactor (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ) :
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) =
      x / ϖ ^ valuationMap K (Additive.ofMul x) :=
  integerUnitOfValuationMapZero_spec K
    (x / ϖ ^ valuationMap K (Additive.ofMul x))
    (uniformizerUnitFactorValuationZero K ϖ x hϖ)

/-- Standard local-field unit/uniformizer decomposition in multiplicative form. -/
theorem uniformizerUnitFactor_mul_uniformizer_zpow (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ) :
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) *
        ϖ ^ valuationMap K (Additive.ofMul x) = x := by
  simp [div_eq_mul_inv, mul_assoc]

/-- Existence form of the standard decomposition `Kˣ = O_Kˣ · ⟨ϖ⟩`. -/
theorem exists_integerUnit_mul_uniformizer_zpow (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ) :
    ∃ u : 𝒪[K]ˣ,
      integerUnitsToFieldUnits K u *
        ϖ ^ valuationMap K (Additive.ofMul x) = x :=
  ⟨uniformizerUnitFactor K ϖ hϖ x,
    uniformizerUnitFactor_mul_uniformizer_zpow K ϖ hϖ x⟩

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
