module

public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# The endomorphism-ring equivalence: endomorphisms and automorphisms of division modules

For the standard equal-characteristic Lubin--Tate module, scalar brackets
identify the endomorphism ring of the level-`m` division module with
`κ⟦T⟧/(T^m)`, and its automorphism group with the quotient of `κ⟦T⟧ˣ` by
the `m`-th higher unit subgroup.  The division-tower sources use a primitive
polynomial indexed by `n` for division level `m = n + 1`; every statement below
keeps this shift explicit.
-/

noncomputable section


open scoped PowerSeries LaurentSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

attribute [local instance]
  equalCharacteristicLubinTateTruncatedSelfSMul
  equalCharacteristicLubinTateTruncatedSelfModule







































































































section
variable (F : LocalField.{u, v} K) (n : ℕ)
include F n
/-- Reduction of integral coefficients modulo `T^(n+1)`. -/
noncomputable def equalCharacteristicLubinTateTruncatedQuotientMap
      :
    F.residueField⟦X⟧ →+* equalCharacteristicLubinTateTruncatedRing F n :=
  equalCharacteristicLubinTateTruncatedRingMk F n

/-- Reduction of integral units modulo `T^(n+1)`. -/
noncomputable def equalCharacteristicLubinTateUnitReduction
      :
    F.residueField⟦X⟧ˣ →*
      (equalCharacteristicLubinTateTruncatedRing F n)ˣ :=
  Units.map (equalCharacteristicLubinTateTruncatedQuotientMap F n)

/-- The value of a reduced unit is the truncated class of its power series. -/
@[simp]
theorem equalCharacteristicLubinTateUnitReduction_val
     
    (u : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicLubinTateUnitReduction F n u :
        equalCharacteristicLubinTateTruncatedRing F n) =
      equalCharacteristicLubinTateTruncatedRingMk F n
        (u : F.residueField⟦X⟧) :=
  rfl

/-- The equal-characteristic realization of the higher unit group
`U_K^(n+1)`: units congruent to one modulo `T^(n+1)`. -/
noncomputable def equalCharacteristicLubinTateHigherUnitSubgroup
      :
    Subgroup F.residueField⟦X⟧ˣ :=
  MonoidHom.ker (equalCharacteristicLubinTateUnitReduction F n)

/-- A unit is in the higher-unit kernel exactly when it is one modulo `X ^ (n + 1)`. -/
theorem mem_equalCharacteristicLubinTateHigherUnitSubgroup
     
    (u : F.residueField⟦X⟧ˣ) :
    u ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n ↔
      (u : F.residueField⟦X⟧) - 1 ∈
        Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧) := by
  constructor
  · intro hu
    have hval := congrArg Units.val hu
    change equalCharacteristicLubinTateTruncatedQuotientMap F n
        (u : F.residueField⟦X⟧) = 1 at hval
    rw [← map_one (equalCharacteristicLubinTateTruncatedQuotientMap F n)] at hval
    exact (equalCharacteristicLubinTateTruncatedRingMk_eq_iff
      F n (u : F.residueField⟦X⟧) 1).mp hval
  · intro hu
    apply Units.ext
    change equalCharacteristicLubinTateTruncatedQuotientMap F n
        (u : F.residueField⟦X⟧) = 1
    rw [← map_one (equalCharacteristicLubinTateTruncatedQuotientMap F n)]
    exact (equalCharacteristicLubinTateTruncatedRingMk_eq_iff
      F n (u : F.residueField⟦X⟧) 1).mpr hu

 theorem equalCharacteristicLubinTateTruncationIdeal_le_constantCoeff_ker
      :
    Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧) ≤
      RingHom.ker (PowerSeries.constantCoeff (R := F.residueField)) := by
  rw [Ideal.span_le]
  intro a ha
  rw [Set.mem_singleton_iff.mp ha]
  change PowerSeries.constantCoeff
      (PowerSeries.X ^ (n + 1) : F.residueField⟦X⟧) = 0
  simp

/-- Constant coefficient descends to every positive truncated power-series
ring. -/
noncomputable def equalCharacteristicLubinTateTruncatedConstantCoeff
      :
    equalCharacteristicLubinTateTruncatedRing F n →+* F.residueField :=
  equalCharacteristicLubinTateTruncatedRingLift F n
    (PowerSeries.constantCoeff (R := F.residueField))
    fun _ ha => RingHom.mem_ker.mp
      (equalCharacteristicLubinTateTruncationIdeal_le_constantCoeff_ker F n ha)

/-- The descended constant-coefficient map evaluates any truncated representative. -/
@[simp]
theorem equalCharacteristicLubinTateTruncatedConstantCoeff_mk
      (f : F.residueField⟦X⟧) :
    equalCharacteristicLubinTateTruncatedConstantCoeff F n
        (equalCharacteristicLubinTateTruncatedRingMk F n f) =
      PowerSeries.constantCoeff f :=
  rfl

/-- Every unit modulo `T^(n+1)` has a power-series unit lift. -/
theorem equalCharacteristicLubinTateUnitReduction_surjective
      :
    Function.Surjective (equalCharacteristicLubinTateUnitReduction F n) := by
  intro u
  obtain ⟨f, hf⟩ := equalCharacteristicLubinTateTruncatedRingMk_surjective
    F n (u : equalCharacteristicLubinTateTruncatedRing F n)
  have hconstant : IsUnit (PowerSeries.constantCoeff f) := by
    have hu : IsUnit
        (equalCharacteristicLubinTateTruncatedConstantCoeff F n
          (u : equalCharacteristicLubinTateTruncatedRing F n)) :=
      u.isUnit.map (equalCharacteristicLubinTateTruncatedConstantCoeff F n)
    rw [← hf] at hu
    simpa only [equalCharacteristicLubinTateTruncatedConstantCoeff_mk] using hu
  have hfUnit : IsUnit f :=
    PowerSeries.isUnit_iff_constantCoeff.mpr hconstant
  let fu : F.residueField⟦X⟧ˣ := hfUnit.unit
  refine ⟨fu, ?_⟩
  apply Units.ext
  change equalCharacteristicLubinTateTruncatedQuotientMap F n
      (fu : F.residueField⟦X⟧) =
    (u : equalCharacteristicLubinTateTruncatedRing F n)
  rw [hfUnit.unit_spec]
  exact hf

/-- The canonical first-isomorphism-theorem identification
`U_K/U_K^(n+1) ≃ (κ⟦T⟧/(T^(n+1)))ˣ`. -/
noncomputable def equalCharacteristicLubinTateUnitQuotientEquivTruncatedUnits
      :
    F.residueField⟦X⟧ˣ ⧸
        equalCharacteristicLubinTateHigherUnitSubgroup F n ≃*
      (equalCharacteristicLubinTateTruncatedRing F n)ˣ :=
  QuotientGroup.quotientKerEquivOfSurjective
    (equalCharacteristicLubinTateUnitReduction F n)
    (equalCharacteristicLubinTateUnitReduction_surjective F n)

/-- The higher-unit quotient equivalence sends a unit class to its truncation. -/
@[simp]
theorem equalCharacteristicLubinTateUnitQuotientEquivTruncatedUnits_mk
     
    (u : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateUnitQuotientEquivTruncatedUnits F n
        (QuotientGroup.mk u) =
      equalCharacteristicLubinTateUnitReduction F n u :=
  rfl
end

























































end EqualCharacteristic
end LubinTate

end
