module

public import ValuedFieldTheory.Valuation.AbsoluteValue.Theory.AbsoluteValues
public import ValuedFieldTheory.Valuation.AbsoluteValue.Theory.ExponentialValuations

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-! Provides the public declarations in the `ValuationTheory.AbsoluteValue.Theory` Lean module. -/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace LubinTate
namespace Valuations

/-- The higher-unit condition `u ∈ 1 + π^n𝒪`. -/
def HigherUnit {O : Type*} [CommRing O] (π : O) (n : ℕ) (u : Oˣ) : Prop :=
  ∃ a : O, (u : O) = 1 + π ^ n * a

/-- The higher-unit condition is equivalently `u - 1 ∈ π^n𝒪`. -/
theorem higherUnit_iff_sub_one_mem_powerIdeal {O : Type*} [CommRing O]
    (π : O) (n : ℕ) (u : Oˣ) :
    HigherUnit π n u ↔ (u : O) - 1 ∈ uniformizerPowerIdeal π n := by
  constructor
  · rintro ⟨a, ha⟩
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton']
    refine ⟨a, ?_⟩
    rw [ha]
    ring
  · intro hu
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton'] at hu
    rcases hu with ⟨a, ha⟩
    use a
    calc
      (u : O) = 1 + ((u : O) - 1) := by ring
      _ = 1 + a * π ^ n := by rw [← ha]
      _ = 1 + π ^ n * a := by ring

/-- The higher unit group `U⁽ⁿ⁾ = 1 + π^n𝒪`, as an actual subgroup of `Oˣ`. -/
def higherUnitSubgroup {O : Type*} [CommRing O] (π : O) (n : ℕ) : Subgroup Oˣ where
  carrier := {u | HigherUnit π n u}
  one_mem' := by
    use 0
    simp
  mul_mem' := by
    rintro u v ⟨a, ha⟩ ⟨b, hb⟩
    use a + b + π ^ n * a * b
    calc
      ((u * v : Oˣ) : O) = (u : O) * (v : O) := rfl
      _ = (1 + π ^ n * a) * (1 + π ^ n * b) := by rw [ha, hb]
      _ = 1 + π ^ n * (a + b + π ^ n * a * b) := by ring
  inv_mem' := by
    rintro u ⟨a, ha⟩
    use -((u⁻¹ : Oˣ) : O) * a
    have hmul : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := by
      simp
    calc
      ((u⁻¹ : Oˣ) : O) =
          ((u⁻¹ : Oˣ) : O) * (u : O) -
            ((u⁻¹ : Oˣ) : O) * ((u : O) - 1) := by
        ring
      _ = 1 - ((u⁻¹ : Oˣ) : O) * ((u : O) - 1) := by
        rw [hmul]
      _ = 1 + π ^ n * (-((u⁻¹ : Oˣ) : O) * a) := by
        rw [ha]
        ring

/-- Membership in a higher-unit subgroup is characterized by proximity to one at the given level. -/
@[simp]
theorem mem_higherUnitSubgroup {O : Type*} [CommRing O]
    {π : O} {n : ℕ} {u : Oˣ} :
    u ∈ higherUnitSubgroup π n ↔ HigherUnit π n u :=
  Iff.rfl

/-- Membership in the higher-unit subgroup is equivalently `u - 1 ∈ π^n𝒪`. -/
theorem mem_higherUnitSubgroup_iff_sub_one_mem_powerIdeal
    {O : Type*} [CommRing O] {π : O} {n : ℕ} {u : Oˣ} :
    u ∈ higherUnitSubgroup π n ↔ (u : O) - 1 ∈ uniformizerPowerIdeal π n := 
  Iff.trans mem_higherUnitSubgroup
    (higherUnit_iff_sub_one_mem_powerIdeal π n u)

/-- The higher-unit filtration is decreasing for arbitrary comparable indices. -/
theorem higherUnitSubgroup_le_of_le {O : Type*} [CommRing O]
    (π : O) {m n : ℕ} (hmn : m ≤ n) :
    higherUnitSubgroup π n ≤ higherUnitSubgroup π m := by
  rintro u ⟨a, ha⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  use π ^ k * a
  calc
    (u : O) = 1 + π ^ (m + k) * a := ha
    _ = 1 + π ^ m * (π ^ k * a) := by
      rw [pow_add]
      ring

/-- Reduction of units modulo an ideal. -/
def unitReduction {O : Type*} [CommRing O] (I : Ideal O) : Oˣ →* (O ⧸ I)ˣ :=
  Units.map (Ideal.Quotient.mk I).toMonoidHom

/-- Unit reduction is the residue of the underlying valuation-ring unit. -/
@[simp]
theorem unitReduction_apply {O : Type*} [CommRing O] (I : Ideal O) (u : Oˣ) :
    (unitReduction I u : O ⧸ I) = Ideal.Quotient.mk I (u : O) :=
  rfl

/-- The kernel of reduction modulo `π^n𝒪` is the higher unit group `1 + π^n𝒪`. -/
theorem unitReduction_ker_powerIdeal {O : Type*} [CommRing O]
    (π : O) (n : ℕ) :
    (unitReduction (uniformizerPowerIdeal π n)).ker = higherUnitSubgroup π n := by
  ext u
  constructor
  · intro hu
    have hval :
        Ideal.Quotient.mk (uniformizerPowerIdeal π n) (u : O) = 1 := by
      simpa [unitReduction] using congrArg Units.val hu
    have hmem : (u : O) - 1 ∈ uniformizerPowerIdeal π n := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp [map_sub, hval]
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton] at hmem
    rcases hmem with ⟨a, ha⟩
    use a
    calc
      (u : O) = 1 + ((u : O) - 1) := by ring
      _ = 1 + π ^ n * a := by rw [ha]
  · rintro ⟨a, ha⟩
    rw [MonoidHom.mem_ker]
    ext
    change Ideal.Quotient.mk (uniformizerPowerIdeal π n) (u : O) = 1
    rw [ha]
    rw [← (Ideal.Quotient.mk (uniformizerPowerIdeal π n)).map_one]
    apply Ideal.Quotient.eq.mpr
    have hπ : π ^ n ∈ uniformizerPowerIdeal π n :=
      Ideal.subset_span (by simp)
    simpa using (uniformizerPowerIdeal π n).mul_mem_right a hπ

/-- A local quotient map induces a surjection on unit groups. -/
theorem unitReduction_surjective_of_isLocalHom {O : Type*} [CommRing O]
    (I : Ideal O) [IsLocalHom (Ideal.Quotient.mk I)] :
    Function.Surjective (unitReduction I) := 
  IsLocalRing.surjective_units_map_of_local_ringHom
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective inferInstance

/-- The first-isomorphism-theorem form of the unit quotient modulo `π^n𝒪`. -/
def unitsModPowerIdealEquivOfSurjective {O : Type*} [CommRing O]
    (π : O) (n : ℕ)
    (hsurj : Function.Surjective (unitReduction (uniformizerPowerIdeal π n))) :
    Oˣ ⧸ higherUnitSubgroup π n ≃* (O ⧸ uniformizerPowerIdeal π n)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq
      (unitReduction_ker_powerIdeal π n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (unitReduction (uniformizerPowerIdeal π n)) hsurj)

/-- For `n ≥ 1`, the ideal `π^n𝒪` is contained in `(π)`. -/
theorem uniformizerPowerIdeal_le_span_singleton {O : Type*} [CommRing O]
    {π : O} {n : ℕ} (hn : 1 ≤ n) :
    uniformizerPowerIdeal π n ≤ Ideal.span ({π} : Set O) := by
  cases n with
  | zero => cases hn
  | succ n =>
      rw [uniformizerPowerIdeal, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      simp

/-- In a DVR, `π^n𝒪` lies in the Jacobson radical for `n ≥ 1` and `π` irreducible. -/
theorem uniformizerPowerIdeal_le_jacobson_bot {O : Type*}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    uniformizerPowerIdeal π n ≤ Ideal.jacobson (⊥ : Ideal O) := by
  have hmax : (Ideal.span ({π} : Set O)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hπ
  have hspan : Ideal.span ({π} : Set O) = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal hmax
  exact (uniformizerPowerIdeal_le_span_singleton (π := π) hn).trans
    (by rw [hspan]; exact IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal O))

/-- The quotient map modulo `π^n𝒪` is local in a DVR, for `n ≥ 1`. -/
theorem unitReduction_isLocalHom_of_dvr {O : Type*}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    IsLocalHom (Ideal.Quotient.mk (uniformizerPowerIdeal π n)) :=
  isLocalHom_of_le_jacobson_bot (uniformizerPowerIdeal π n)
    (uniformizerPowerIdeal_le_jacobson_bot hπ hn)

/-- The unit-reduction and graded-piece equivalences, surjectivity part for the reduction map on unit groups. -/
theorem units_reduction_surjective
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    Function.Surjective (unitReduction (uniformizerPowerIdeal π n)) := by
  let : IsLocalHom (Ideal.Quotient.mk (uniformizerPowerIdeal π n)) :=
    unitReduction_isLocalHom_of_dvr hπ hn
  exact unitReduction_surjective_of_isLocalHom (uniformizerPowerIdeal π n)

/-- The unit-reduction and graded-piece equivalences, the named first-isomorphism-theorem equivalence
`Oˣ/U⁽ⁿ⁾ ≃ (O/π^nO)ˣ`. -/
def units_quotient_equiv
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    Oˣ ⧸ higherUnitSubgroup π n ≃* (O ⧸ uniformizerPowerIdeal π n)ˣ := 
  unitsModPowerIdealEquivOfSurjective π n
    (units_reduction_surjective hπ hn)

/-- The unit-quotient equivalence of the unit-reduction and graded-piece equivalences is induced by
reduction modulo `πⁿO`. -/
@[simp]
theorem units_quotient_equiv_mk
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) (u : Oˣ) :
    units_quotient_equiv hπ hn (QuotientGroup.mk u) =
      unitReduction (uniformizerPowerIdeal π n) u := by
  rfl
