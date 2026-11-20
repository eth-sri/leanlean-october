module

public import Mathlib.FieldTheory.Galois.Basic
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.Valuation` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open IsNonarchimedeanLocalField

section

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The actual `Gal(L / K)` action on field units, obtained by applying each
field automorphism to a unit. -/
@[implicit_reducible]
def galoisGroupFieldUnitsMulDistribMulAction :
    MulDistribMulAction (Gal(L / K)) Lˣ where
  smul σ x := Units.mapEquiv σ.toMulEquiv x
  one_smul := by
    intro x
    ext
    rfl
  mul_smul := by
    intro σ τ x
    ext
    rfl
  smul_mul := fun σ x y => map_mul (Units.mapEquiv σ.toMulEquiv) x y
  smul_one := fun σ => map_one (Units.mapEquiv σ.toMulEquiv)

/-- States the theorem `galoisGroupFieldUnitsMulDistribMulAction_smul`. -/
@[simp]
theorem galoisGroupFieldUnitsMulDistribMulAction_smul
    (σ : Gal(L / K)) (x : Lˣ) :
    letI := galoisGroupFieldUnitsMulDistribMulAction K L
    σ • x = Units.mapEquiv σ.toMulEquiv x :=
  rfl

end

section

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- The actual `Gal(L / K)` action on integer units.  Its source is the
restriction of the field automorphism to the integral closure `𝒪[L]`. -/
@[implicit_reducible]
def galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure :
    MulDistribMulAction (Gal(L / K)) 𝒪[L]ˣ where
  smul σ x := Units.mapEquiv
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv x
  one_smul := by
    intro x
    ext
    rfl
  mul_smul := by
    intro σ τ x
    ext
    rfl
  smul_mul := fun σ x y => map_mul
      (Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv) x y
  smul_one := fun σ => map_one
      (Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv)

/-- States the theorem `galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul`. -/
@[simp]
theorem galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul
    (σ : Gal(L / K)) (x : 𝒪[L]ˣ) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    σ • x = Units.mapEquiv
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv x :=
  rfl

end

section

variable (K L : Type u) [Field K]

/-- The trivial Galois action on the value group `ℤ`, written
multiplicatively so that it is a multiplicative Galois module. -/
@[implicit_reducible]
def galoisGroupValueGroupMulDistribMulAction [Field L] [Algebra K L] :
    MulDistribMulAction (Gal(L / K)) (Multiplicative Int) where
  smul _ n := n
  one_smul := by intro n; rfl
  mul_smul := by intro _ _ n; rfl
  smul_mul := by intro _ m n; rfl
  smul_one := by intro _; rfl

/-- States the theorem `galoisGroupValueGroupMulDistribMulAction_smul`. -/
@[simp]
theorem galoisGroupValueGroupMulDistribMulAction_smul [Field L] [Algebra K L]
    (σ : Gal(L / K)) (n : Multiplicative Int) :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    σ • n = n :=
  rfl

/-- The inclusion `𝒪_Lˣ → Lˣ` is equivariant for the actual actions. -/
theorem integerUnitsToFieldUnits_galoisGroup_equivariant [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) (x : 𝒪[L]ˣ) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := galoisGroupFieldUnitsMulDistribMulAction K L
    integerUnitsToFieldUnits L (σ • x) =
      σ • integerUnitsToFieldUnits L x := by
  rfl

end

section

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) (x : Lˣ)

/-- A Galois automorphism preserves the normalized additive valuation.  The
proof uses only the actual integral-closure restriction to `𝒪_L`, the DVR
normalization of an irreducible uniformizer, and the unit--uniformizer
decomposition of `Lˣ`; no extension-invariant package is assumed. -/
theorem valuationMap_unitsMapEquiv_galoisGroup :
    valuationMap L
        (Additive.ofMul (Units.mapEquiv σ.toMulEquiv x)) =
      valuationMap L (Additive.ofMul x) := by
  let e := galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
  let πO := chosenIntegerRingUniformizer L
  let σπ := Units.mapEquiv σ.toMulEquiv (integerRingUniformizerFieldUnit L)
  have hvσπinv : v L (Additive.ofMul σπ⁻¹) = 1 := by
    rw [v_inv, (v_integerRingIrreducibleFieldUnit L (e πO) ((MulEquiv.irreducible_iff e.toMulEquiv).2
      (chosenIntegerRingUniformizer_irreducible L)) σπ rfl)]
    norm_num
  let ϖ := inverseIntegerRingUniformizerFieldUnit L
  have hmapϖ : Units.mapEquiv σ.toMulEquiv ϖ = σπ⁻¹ := by
    ext
    rfl
  have hvmapϖ :
      v L (Additive.ofMul (Units.mapEquiv σ.toMulEquiv ϖ)) = 1 := by
    rw [hmapϖ]
    exact hvσπinv
  have hϖ : valuationMap L (Additive.ofMul ϖ) = 1 := by
    exact v_inverseIntegerRingUniformizerFieldUnit L
  let n : Int := valuationMap L (Additive.ofMul x)
  let u : 𝒪[L]ˣ := uniformizerUnitFactor L ϖ hϖ x
  let σu : 𝒪[L]ˣ := Units.mapEquiv e.toMulEquiv u
  have hmapu :
      Units.mapEquiv σ.toMulEquiv (integerUnitsToFieldUnits L u) =
        integerUnitsToFieldUnits L σu := by
    ext
    rfl
  have hvmapu :
      v L (Additive.ofMul
        (Units.mapEquiv σ.toMulEquiv (integerUnitsToFieldUnits L u))) = 0 := by
    rw [hmapu]
    exact v_integerUnitsToFieldUnits L σu
  have hx : integerUnitsToFieldUnits L u * ϖ ^ n = x := by
    simp [u, n]
  have hxσ :
      Units.mapEquiv σ.toMulEquiv x =
        Units.mapEquiv σ.toMulEquiv (integerUnitsToFieldUnits L u) *
          (Units.mapEquiv σ.toMulEquiv ϖ) ^ n := by
    calc
      Units.mapEquiv σ.toMulEquiv x =
          Units.mapEquiv σ.toMulEquiv
            (integerUnitsToFieldUnits L u * ϖ ^ n) :=
        congrArg (Units.mapEquiv σ.toMulEquiv) hx.symm
      _ = Units.mapEquiv σ.toMulEquiv (integerUnitsToFieldUnits L u) *
          (Units.mapEquiv σ.toMulEquiv ϖ) ^ n := by
        simp
  rw [valuationMap_apply, valuationMap_apply, hxσ, v_mul, v_zpow,
    hvmapu, hvmapϖ, mul_one, zero_add]
  rfl

/-- The normalized valuation on `Lˣ` is equivariant for the actual Galois
action and the trivial action on its value group. -/
theorem valuationUnitsMulHom_galoisGroup_equivariant :
    letI := galoisGroupFieldUnitsMulDistribMulAction K L
    letI := galoisGroupValueGroupMulDistribMulAction K L
    valuationUnitsMulHom L (σ • x) =
      σ • valuationUnitsMulHom L x := by
  exact congrArg Multiplicative.ofAdd
    (valuationMap_unitsMapEquiv_galoisGroup K L σ x)

end

variable (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

/-- Multiplicative and additive presentations of valuation-one/valuation-zero
agree for a field unit. -/
theorem valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zero (x : Lˣ) :
    valuationUnitsMulHom L x = 1 ↔
      valuationMap L (Additive.ofMul x) = 0 := by
  rfl

/-- Exactness at `Lˣ`: the kernel of normalized valuation consists exactly
of the units of the valuation integer ring. -/
theorem valuationUnitsMulHom_eq_one_iff_exists_integerUnit (x : Lˣ) :
    valuationUnitsMulHom L x = 1 ↔
      ∃ y : 𝒪[L]ˣ, integerUnitsToFieldUnits L y = x := by
  rw [valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zero]
  constructor
  · intro hx
    exact
      (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero L x).2 hx
  · rintro ⟨y, rfl⟩
    exact
      (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero L
        (integerUnitsToFieldUnits L y)).1 ⟨y, rfl⟩

/-- The multiplicative normalized valuation `Lˣ → Multiplicative ℤ` is
surjective. -/
theorem valuationUnitsMulHom_surjective :
    Function.Surjective (valuationUnitsMulHom L) := by
  exact valuationMap_surjective L

end
end LocalClassFieldTheory
