/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.ClassGroup.QuadraticInvariantIdeal
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import CCDN.ClassGroup.NumberFieldUnitSquareClasses
import CCDN.ClassGroup.QuadraticNormConjugation
import CCDN.ForMathlib.FieldTheory
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree

/-!
The unit-norm obstruction for ambiguous ideal classes.
Equal obstructions yield classes differing by a class represented by an
invariant fractional ideal. The representatives can be chosen once, so
the fiber argument does not need a preliminary choice-independent
description of the obstruction homomorphism.

The unit-norm quotient in a quadratic extension is finite,
with a uniform bound depending only on the base-field degree. Squares
of base units are norms of their extensions.
-/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped NumberField

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-- The relative norm `N_{K/F}` restricted to unit groups of rings of integers. -/
def relativeUnitNorm : (𝓞 K)ˣ →* (𝓞 F)ˣ :=
  Units.map (RingOfIntegers.norm F)

private theorem relativeUnitNorm_extended (u : (𝓞 F)ˣ) :
    relativeUnitNorm F K (Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom u) =
      u ^ Module.finrank F K := by
  apply Units.ext
  exact RingOfIntegers.norm_algebraMap F u

/-- The unit-norm obstruction group: the units of `𝓞 F` modulo the relative norms of units of
`𝓞 K`. -/
abbrev quadraticUnitNormQuotient :=
  (𝓞 F)ˣ ⧸ (relativeUnitNorm F K).range

private theorem quadraticUnitNormQuotient_square (hd : Module.finrank F K = 2)
    (x : quadraticUnitNormQuotient F K) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom u, ?_⟩
    rw [relativeUnitNorm_extended, hd]

variable [NumberField F]

variable (hd : Module.finrank F K = 2)

include hd in
/-- For a quadratic extension `K / F` of number fields, the unit-norm quotient is finite. -/
theorem quadraticUnitNormQuotient_finite  :
    Finite (quadraticUnitNormQuotient F K) :=
  (numberFieldUnit_exponent_two_quotient F
    (QuotientGroup.mk' (relativeUnitNorm F K).range)
    (QuotientGroup.mk'_surjective _) (quadraticUnitNormQuotient_square F K hd)).1


include hd in
/-- For a quadratic extension `K / F` of number fields, the unit-norm quotient has order at most
`2 ^ [F : ℚ]`. -/
theorem quadraticUnitNormQuotient_card_le_degree  :
    Nat.card (quadraticUnitNormQuotient F K) ≤ 2 ^ Module.finrank ℚ F :=
  (((numberFieldUnit_exponent_two_quotient F
       (QuotientGroup.mk' (relativeUnitNorm F K).range)
       (QuotientGroup.mk'_surjective _) (quadraticUnitNormQuotient_square F K hd)).2)).trans
    (Nat.pow_le_pow_right (by norm_num) (numberField_unit_rank_add_one_le_degree F))

end
end CCDN

namespace CCDN
noncomputable section
open NumberField
open scoped NumberField nonZeroDivisors

section PrincipalUnits
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
private theorem principalIdeal_of_ring_unit (u : Rˣ) :
    toPrincipalIdeal R K (Units.map (algebraMap R K).toMonoidHom u) = 1 := by
  apply Units.ext
  simp only [coe_toPrincipalIdeal, Units.coe_map, Units.val_one]
  change FractionalIdeal.spanSingleton R⁰ (algebraMap R K (u : R)) = 1
  rw [← FractionalIdeal.coeIdeal_span_singleton  ]
  simp only [Ideal.span_singleton_eq_top.mpr u.isUnit, FractionalIdeal.coeIdeal_top]

end PrincipalUnits

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K]

omit [NumberField F] in
private theorem fractionField_ringOfIntegers_automorphism (σ : K ≃ₐ[F] K) :
    (IsFractionRing.ringEquivOfRingEquiv
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv : K ≃+* K) = σ.toRingEquiv := by
  apply RingEquiv.ext
  have h : (IsFractionRing.ringEquivOfRingEquiv
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv : K ≃+* K).toRingHom =
      σ.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := 𝓞 K)
    solve_by_elim [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  exact RingHom.congr_fun h

/-- Classes represented by invariant invertible fractional ideals. -/
def stronglyAmbiguousClassGroup (σ : K ≃ₐ[F] K)  :=
  ((ClassGroup.mk K).comp
    ((fractionalIdealUnitAction 
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv).eqLocus
        (MonoidHom.id _)).subtype).range

omit [NumberField F] in
/-- An ideal class is strongly ambiguous if and only if it is the class of a `σ`-invariant
invertible fractional ideal. -/
theorem mem_stronglyAmbiguousClassGroup (σ : K ≃ₐ[F] K) (c : ClassGroup (𝓞 K)) :
    c ∈ stronglyAmbiguousClassGroup F K σ ↔
      ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
        fractionalIdealUnitAction 
          (RingOfIntegers.mapAlgEquiv σ).toRingEquiv I = I ∧ ClassGroup.mk K I = c := by
  constructor
  · rintro ⟨I, rfl⟩
    exact ⟨I, I.property, rfl⟩
  · rintro ⟨I, hI, rfl⟩
    exact ⟨⟨I, hI⟩, rfl⟩

variable (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)


include hd hσ in
/-- Equality of the concrete unit obstructions places the quotient of
two represented classes in the strongly ambiguous subgroup. -/
theorem equal_unit_obstructions_stronglyAmbiguous
    
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a b : Kˣ)
    (u v : (𝓞 F)ˣ)
    (hI : fractionalIdealUnitAction 
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv I = toPrincipalIdeal (𝓞 K) K a * I)
    (hJ : fractionalIdealUnitAction 
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv J = toPrincipalIdeal (𝓞 K) K b * J)
    (ha : Algebra.norm F (a : K) = ((u : 𝓞 F) : F))
    (hb : Algebra.norm F (b : K) = ((v : 𝓞 F) : F))
    (huv : QuotientGroup.mk (s := (relativeUnitNorm F K).range) u =
      QuotientGroup.mk v) :
    ClassGroup.mk K I / ClassGroup.mk K J ∈ stronglyAmbiguousClassGroup F K σ := by
  have huv' : u / v ∈ (relativeUnitNorm F K).range := by
    apply (QuotientGroup.eq_one_iff _).mp
    rw [QuotientGroup.mk_div, huv, div_self']
  obtain ⟨w, hw⟩ := huv'
  have hnorm : Algebra.norm F ((a / b : Kˣ) : K) =
      Algebra.norm F ((w : 𝓞 K) : K) := by
    have hh := congrArg
      (fun z : (𝓞 F)ˣ => (Units.map (algebraMap (𝓞 F) F).toMonoidHom z)) hw
    rw [map_div] at hh
    have hh := congrArg ((Units.val)) hh
    simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hh
    simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      map_mul, Algebra.norm_inv]
    rw [ha, hb]
    exact hh.symm
  have hquot : fractionalIdealUnitAction 
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv (I / J) =
      toPrincipalIdeal (𝓞 K) K (a / b) * (I / J) := by
    simp_all [map_div, mul_div_mul_comm]
  let inline_I := I / J
  let inline_a := a / b
  let inline_ha := hnorm
  let e : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom w
  have hprincipal : toPrincipalIdeal (𝓞 K) K (inline_a / e) =
      toPrincipalIdeal (𝓞 K) K inline_a := by
    rw [map_div, principalIdeal_of_ring_unit, div_one]
  have hnorm : Algebra.norm F ((inline_a / e : Kˣ) : K) = 1 := by
    simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      map_mul, Algebra.norm_inv]
    change Algebra.norm F (inline_a : K) *
      (Algebra.norm F ((w : 𝓞 K) : K))⁻¹ = 1
    rw [inline_ha, mul_inv_cancel₀]
    apply Algebra.norm_ne_zero_iff.mpr
    exact RingOfIntegers.coe_ne_zero_iff.mpr w.ne_zero
  have hnorm' : ((inline_a / e : Kˣ) : K) *
      σ (((inline_a / e : Kˣ) : K)) = 1 := by
    rw [← quadratic_norm_eq_mul_conjugate F K hd σ hσ, hnorm, map_one]
  have hcompat : ∀ b : Kˣ,
      fractionalIdealUnitAction  (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
        (toPrincipalIdeal (𝓞 K) K b) =
      toPrincipalIdeal (𝓞 K) K (Units.map σ.toRingEquiv.toMonoidHom b) := by
    simp_all [fractionalIdealUnitAction_principal, fractionField_ringOfIntegers_automorphism]
  have hσne : σ.toRingEquiv ≠ RingEquiv.refl K := by
    intro h
    apply hσ
    exact AlgEquiv.ext (RingEquiv.congr_fun h)
  obtain ⟨b, hb⟩ := RingEquiv.exists_invariant_of_involutive σ.toRingEquiv
    (quadratic_automorphism_involutive F K hd σ) hσne
    (fractionalIdealUnitAction  (RingOfIntegers.mapAlgEquiv σ).toRingEquiv)
    (toPrincipalIdeal (𝓞 K) K) hcompat inline_I (inline_a / e)
    (by rw [hprincipal]; exact hquot) hnorm'
  apply (mem_stronglyAmbiguousClassGroup F K σ _).mpr
  refine ⟨toPrincipalIdeal (𝓞 K) K b * inline_I, hb, ?_⟩
  rw [map_mul, classGroup_mk_principal, one_mul]
  simp only [inline_I, map_div]

end
end CCDN
