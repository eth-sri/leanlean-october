module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration
public import Mathlib.Algebra.Group.Units.Equiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

/-!
# Automorphism transport for principal units

A field automorphism preserving the chosen valuation ring acts on the valuation ring,
its residue field, its units, and every principal-unit quotient.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- A field automorphism preserving the chosen valuation ring induces a ring
automorphism of the valuation ring.  This is the unit/residue source used
before invoking local reciprocity in the local-field arguments. -/
def valuationSubringRingEquivOfPreserves
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring) :
    F.valuationSubring ≃+* F.valuationSubring :=
  RingEquiv.restrict e F.valuation.valuationSubring
    F.valuation.valuationSubring hmem

/-- A valuation-ring-preserving field automorphism preserves every power of the
maximal ideal of the chosen valuation ring. -/
theorem valuationSubringRingEquivOfPreserves_mem_maximalIdeal_pow_iff
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) (x : F.valuationSubring) :
    valuationSubringRingEquivOfPreserves F e hmem x ∈ F.maximalIdeal ^ n ↔
      x ∈ F.maximalIdeal ^ n := by
  let r := valuationSubringRingEquivOfPreserves F e hmem
  have hmax :
      F.maximalIdeal.map
          (r : F.valuationSubring →+* F.valuationSubring) =
        F.maximalIdeal :=
    IsLocalRing.map_ringEquiv_maximalIdeal r
  have hmap :
      (F.maximalIdeal ^ n).map (r : F.valuationSubring →+* F.valuationSubring) =
        F.maximalIdeal ^ n := by
    rw [Ideal.map_pow, hmax]
  constructor
  · intro hx
    rw [← hmap] at hx
    rw [Ideal.mem_map_iff_of_surjective
      (r : F.valuationSubring →+* F.valuationSubring) r.surjective] at hx
    rcases hx with ⟨y, hy, hyx⟩
    have hy_eq : y = x := r.injective hyx
    simpa [hy_eq] using hy
  · intro hx
    rw [← hmap]
    exact Ideal.mem_map_of_mem (r : F.valuationSubring →+* F.valuationSubring) hx

/-- The residue-field automorphism induced by a field automorphism preserving
the chosen valuation ring. -/
noncomputable def valuationSubringResidueFieldEquivOfPreserves
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring) :
    F.residueField ≃+* F.residueField := by
  let r := valuationSubringRingEquivOfPreserves F e hmem
  letI : IsLocalHom (r : F.valuationSubring →+* F.valuationSubring) :=
    IsLocalHom.of_surjective (r : F.valuationSubring →+* F.valuationSubring)
      r.surjective
  exact IsLocalRing.ResidueField.mapEquiv r

/--
Establishes the identity `valuationSubringResidueFieldEquivOfPreserves F e hmem (F.residueMap x) =
F.residueMap (valuationSubringRingEquivOfPreserves F e hmem x)`.
-/
@[simp] theorem valuationSubringResidueFieldEquivOfPreserves_apply_residue
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (x : F.valuationSubring) :
    valuationSubringResidueFieldEquivOfPreserves F e hmem (F.residueMap x) =
      F.residueMap (valuationSubringRingEquivOfPreserves F e hmem x) := by
  let r := valuationSubringRingEquivOfPreserves F e hmem
  let : IsLocalHom (r : F.valuationSubring →+* F.valuationSubring) :=
    IsLocalHom.of_surjective (r : F.valuationSubring →+* F.valuationSubring)
      r.surjective
  rfl

/-- The induced automorphism on valuation-ring units. -/
def valuationSubringUnitEquivOfPreserves
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring) :
    F.valuationSubringˣ ≃* F.valuationSubringˣ :=
  Units.mapEquiv
    (valuationSubringRingEquivOfPreserves F e hmem).toMulEquiv

/--
The defining evaluation formula for `valuationSubringUnitEquivOfPreserves` is
`((valuationSubringUnitEquivOfPreserves F e hmem u : F.valuationSubringˣ) : F.valuationSubring) =
valuationSubringRingEquivOfPreserves F e hmem (u : F.valuationSubring)`.
-/
@[simp] theorem valuationSubringUnitEquivOfPreserves_apply
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (u : F.valuationSubringˣ) :
    ((valuationSubringUnitEquivOfPreserves F e hmem u :
        F.valuationSubringˣ) : F.valuationSubring) =
      valuationSubringRingEquivOfPreserves F e hmem
        (u : F.valuationSubring) :=
  rfl



/-- The induced automorphism on valuation-ring units preserves every concrete
principal-unit level `U^n`. -/
theorem valuationSubringUnitEquivOfPreserves_mem_principalUnit_iff
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) (u : F.valuationSubringˣ) :
    valuationSubringUnitEquivOfPreserves F e hmem u ∈
        higherPrincipalUnitGroup F n ↔
      u ∈ higherPrincipalUnitGroup F n := by
  rw [higherPrincipalUnitGroup.mem_iff, higherPrincipalUnitGroup.mem_iff]
  have hsub :
      ((valuationSubringUnitEquivOfPreserves F e hmem u :
          F.valuationSubringˣ) : F.valuationSubring) - 1 =
        valuationSubringRingEquivOfPreserves F e hmem
          ((u : F.valuationSubring) - 1) := by
    simp [valuationSubringUnitEquivOfPreserves_apply]
  rw [hsub]
  exact valuationSubringRingEquivOfPreserves_mem_maximalIdeal_pow_iff F e hmem
    n ((u : F.valuationSubring) - 1)

/-- The subgroup map form of principal-unit preservation for a
valuation-ring-preserving field automorphism. -/
theorem higherPrincipalUnitGroup_map_valuationSubringUnitEquivOfPreserves
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) :
    (higherPrincipalUnitGroup F n).map
        (valuationSubringUnitEquivOfPreserves F e hmem :
          F.valuationSubringˣ →* F.valuationSubringˣ) =
      higherPrincipalUnitGroup F n := by
  let ueq := valuationSubringUnitEquivOfPreserves F e hmem
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (valuationSubringUnitEquivOfPreserves_mem_principalUnit_iff
      F e hmem n v).2 hv
  · intro hu
    refine ⟨ueq.symm u, ?_, by simp [ueq]⟩
    exact (valuationSubringUnitEquivOfPreserves_mem_principalUnit_iff
      F e hmem n (ueq.symm u)).1 (by simpa [ueq] using hu)

/-- A valuation-ring-preserving field automorphism induces an automorphism on
`O^*/U^n` for every concrete principal-unit level. -/
noncomputable def unitsModPrincipalUnitEquivOfPreserves
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) :
    F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n ≃*
      F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n :=
  QuotientGroup.congr (higherPrincipalUnitGroup F n)
    (higherPrincipalUnitGroup F n)
    (valuationSubringUnitEquivOfPreserves F e hmem)
    (higherPrincipalUnitGroup_map_valuationSubringUnitEquivOfPreserves F e hmem n)

/--
Establishes the identity `unitsModPrincipalUnitEquivOfPreserves F e hmem n (QuotientGroup.mk'
(higherPrincipalUnitGroup F n) u) = QuotientGroup.mk' (higherPrincipalUnitGroup F n)
(valuationSubringUnitEquivOfPreserves F e hmem u)`.
-/
@[simp] theorem unitsModPrincipalUnitEquivOfPreserves_mk
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) (u : F.valuationSubringˣ) :
    unitsModPrincipalUnitEquivOfPreserves F e hmem n
        (QuotientGroup.mk' (higherPrincipalUnitGroup F n) u) =
      QuotientGroup.mk' (higherPrincipalUnitGroup F n)
        (valuationSubringUnitEquivOfPreserves F e hmem u) :=
  rfl












end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
