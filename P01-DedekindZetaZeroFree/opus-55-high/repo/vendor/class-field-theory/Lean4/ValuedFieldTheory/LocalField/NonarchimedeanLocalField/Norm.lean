module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Valuation.Integral
public import ValuedFieldTheory.LocalField.NormUnits
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuativeExtension
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-!
# Norms in valued field extensions

Packages field norms as homomorphisms on units and restricts them to valuation
rings and their unit groups under the appropriate integral hypotheses.
-/


namespace LocalFieldTheory

noncomputable section

universe u v

namespace IsNonarchimedeanLocalField

open scoped BigOperators ValuativeRel

variable {K : Type u} {L : Type v}


section UnitNorm

variable [Field K] [Field L] [Algebra K L]

/-- Base units embedded in an extension. -/
def mapBaseUnitsToExtensionUnits
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Kˣ →* Lˣ :=
  Units.map (algebraMap K L).toMonoidHom

/-- The inclusion of base-field units into extension-field units agrees with the algebra map on
underlying elements. -/
@[simp]
lemma mapBaseUnitsToExtensionUnits_apply_coe (x : Kˣ) :
    ((mapBaseUnitsToExtensionUnits K L x : Lˣ) : L) = algebraMap K L (x : K) :=
  rfl

/-- The unit norm of an embedded base unit is the degree-th power of that base unit. -/
lemma normUnits_algebraMap_base (x : Kˣ) :
    normUnits K L (mapBaseUnitsToExtensionUnits K L x) =
      Units.map (MonoidHom.id K) (x ^ Module.finrank K L) := by
  ext
  simp

/-- The norm of an element integral over the base valuation ring lies in the base valuation ring. -/
lemma algebraNorm_mem_integers_of_mem_integers [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]) :
    Algebra.norm K (x : L) ∈ 𝒪[K] := 
  Valuation.Integers.mem_of_integral
    (Valuation.integer.integers (ValuativeRel.valuation K))
    (Algebra.isIntegral_norm K (LocalFieldTheory.ValuativeExtension.integer_isIntegral x))

/-- Defines `normIntegerUnitsValue`. -/
def normIntegerUnitsValue [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) : 𝒪[K] :=
  ⟨Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L),
    algebraNorm_mem_integers_of_mem_integers ((x : 𝒪[L]ˣ) : 𝒪[L])⟩

/-- The norm value constructed from an integer unit multiplied by its inverse is one. -/
lemma normIntegerUnitsValue_mul_inv [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) :
    normIntegerUnitsValue (K := K) (L := L) x *
      normIntegerUnitsValue (K := K) (L := L) x⁻¹ = 1 := by
  ext
  change Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      Algebra.norm K (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
  have hx : (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1 := by
    change (((x * x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
    simp
  rw [← map_mul (Algebra.norm K)]
  simp [hx]

/-- The inverse norm value multiplied by the norm value of an integer unit is one. -/
lemma normIntegerUnitsValue_inv_mul [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) :
    normIntegerUnitsValue (K := K) (L := L) x⁻¹ *
      normIntegerUnitsValue (K := K) (L := L) x = 1 := by
  ext
  change Algebra.norm K (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
  have hx : (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1 := by
    change (((x⁻¹ * x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
    simp
  rw [← map_mul (Algebra.norm K)]
  simp [hx]

/-- Norm restricted to valuation-integer units. -/
def normIntegerUnits
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [LocalFieldTheory.ValuativeExtension K L] : 𝒪[L]ˣ →* 𝒪[K]ˣ where
  toFun := fun x => {
    val := normIntegerUnitsValue (K := K) (L := L) x
    inv := normIntegerUnitsValue (K := K) (L := L) x⁻¹
    val_inv := normIntegerUnitsValue_mul_inv (K := K) (L := L) x
    inv_val := normIntegerUnitsValue_inv_mul (K := K) (L := L) x
  }
  map_one' := by
    ext
    simp [normIntegerUnitsValue]
  map_mul' := by
    intro x y
    ext
    simp [normIntegerUnitsValue]

/-- Coercing the integer-unit norm to the base field yields the algebra norm of the original unit. -/
lemma normIntegerUnits_apply_coe [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) :
    (((normIntegerUnits K L x : 𝒪[K]ˣ) : 𝒪[K]) : K) =
      Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) :=
  rfl

end UnitNorm

section Valuation

variable [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
variable [Algebra K L]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- For a finite Galois extension, embedding the unit norm back into the extension equals the
product of all Galois conjugates. -/
lemma mapBaseUnits_normUnits_eq_prod_gal [FiniteDimensional K L] [IsGalois K L]
    (x : Lˣ) :
    mapBaseUnitsToExtensionUnits K L (normUnits K L x) =
      ∏ σ : L ≃ₐ[K] L, Units.mapEquiv σ.toMulEquiv x := by
  ext
  simp [mapBaseUnitsToExtensionUnits, normUnits, Algebra.norm_eq_prod_automorphisms]
