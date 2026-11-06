/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ClassGroup.QuadraticInvariantIdeal
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
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

namespace CCDN
noncomputable section
open NumberField
open scoped NumberField

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-- The relative norm `N_{K/F}` restricted to unit groups of rings of integers. -/
def relativeUnitNorm : (𝓞 K)ˣ →* (𝓞 F)ˣ :=
  Units.map (RingOfIntegers.norm F)

theorem relativeUnitNorm_extended (u : (𝓞 F)ˣ) :
    relativeUnitNorm F K (Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom u) =
      u ^ Module.finrank F K := by
  apply Units.ext
  exact RingOfIntegers.norm_algebraMap F u

/-- The unit-norm obstruction group: the units of `𝓞 F` modulo the relative norms of units of
`𝓞 K`. -/
abbrev quadraticUnitNormQuotient :=
  (𝓞 F)ˣ ⧸ (relativeUnitNorm F K).range

theorem quadraticUnitNormQuotient_square (hd : Module.finrank F K = 2)
    (x : quadraticUnitNormQuotient F K) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom u, ?_⟩
    rw [relativeUnitNorm_extended, hd]

variable [NumberField F]

variable (hd : Module.finrank F K = 2)
include hd

/-- For a quadratic extension `K / F` of number fields, the unit-norm quotient is finite. -/
theorem quadraticUnitNormQuotient_finite :
    Finite (quadraticUnitNormQuotient F K) :=
  (numberFieldUnit_exponent_two_quotient F
    (QuotientGroup.mk' (relativeUnitNorm F K).range)
    (QuotientGroup.mk'_surjective _) (quadraticUnitNormQuotient_square F K hd)).1

/-- For a quadratic extension `K / F` of number fields, the unit-norm quotient has order at most
`2 ^ [F : ℚ]`. -/
theorem quadraticUnitNormQuotient_card_le_degree :
    Nat.card (quadraticUnitNormQuotient F K) ≤ 2 ^ Module.finrank ℚ F :=
  (numberFieldUnit_exponent_two_quotient F
    (QuotientGroup.mk' (relativeUnitNorm F K).range)
    (QuotientGroup.mk'_surjective _) (quadraticUnitNormQuotient_square F K hd)).2.trans
    (Nat.pow_le_pow_right (by norm_num) (show NumberField.Units.rank F + 1 ≤ Module.finrank ℚ F by
        have hpos := Fintype.card_pos (α := InfinitePlace F)
        have hcard := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
        have hrank := InfinitePlace.card_add_two_mul_card_eq_rank (K := F)
        unfold NumberField.Units.rank
        omega))

end

noncomputable section
open NumberField
open scoped NumberField nonZeroDivisors

section PrincipalUnits
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
theorem principalIdeal_of_ring_unit (u : Rˣ) :
    toPrincipalIdeal R K (Units.map (algebraMap R K).toMonoidHom u) = 1 := by
  apply Units.ext
  simp
  rw [← FractionalIdeal.coeIdeal_span_singleton]
  simp [Ideal.span_singleton_eq_top.mpr u.isUnit, FractionalIdeal.coeIdeal_top]

end PrincipalUnits

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K]

omit [NumberField F] in
section
variable (σ : K ≃ₐ[F] K)

theorem fractionField_ringOfIntegers_automorphism :
    (IsFractionRing.ringEquivOfRingEquiv
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv : K ≃+* K) = σ.toRingEquiv := by
  apply RingEquiv.ext
  have h : (IsFractionRing.ringEquivOfRingEquiv
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv : K ≃+* K).toRingHom =
      σ.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := 𝓞 K)
    intro x
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv x
  exact RingHom.congr_fun h

/-- Classes represented by invariant invertible fractional ideals. -/
def stronglyAmbiguousClassGroup : Subgroup (ClassGroup (𝓞 K)) :=
  ((ClassGroup.mk K).comp
    ((fractionalIdealUnitAction (K := K)
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv).eqLocus
        (MonoidHom.id _)).subtype).range

end

omit [NumberField F] in
/-- An ideal class is strongly ambiguous if and only if it is the class of a `σ`-invariant
invertible fractional ideal. -/
theorem mem_stronglyAmbiguousClassGroup (σ : K ≃ₐ[F] K) (c : ClassGroup (𝓞 K)) :
    c ∈ stronglyAmbiguousClassGroup F K σ ↔
      ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
        fractionalIdealUnitAction (K := K)
          (RingOfIntegers.mapAlgEquiv σ).toRingEquiv I = I ∧ ClassGroup.mk K I = c := by
  constructor
  · rintro ⟨I, rfl⟩
    aesop
  · tauto

variable (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
include hd hσ

/-- A scalar comparison whose norm is the norm of an integer unit has
trivial obstruction and admits an invariant representative. -/
theorem exists_invariant_ideal_of_scalar_norm_unit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) (u : (𝓞 K)ˣ)
    (hI : fractionalIdealUnitAction (K := K)
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv I = toPrincipalIdeal (𝓞 K) K a * I)
    (ha : Algebra.norm F (a : K) = Algebra.norm F ((u : 𝓞 K) : K)) :
    ClassGroup.mk K I ∈ stronglyAmbiguousClassGroup F K σ := by
  let e : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom u
  have hprincipal : toPrincipalIdeal (𝓞 K) K (a / e) =
      toPrincipalIdeal (𝓞 K) K a := by
    rw [map_div, principalIdeal_of_ring_unit, div_one]
  have hnorm : Algebra.norm F ((a / e : Kˣ) : K) = 1 := by
    simp [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      map_mul, Algebra.norm_inv]
    aesop
  have hnorm' : ((a / e : Kˣ) : K) *
      σ (((a / e : Kˣ) : K)) = 1 := by
    rw [← quadratic_norm_eq_mul_conjugate F K hd σ hσ, hnorm, map_one]
  have hcompat : ∀ b : Kˣ,
      fractionalIdealUnitAction (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
        (toPrincipalIdeal (𝓞 K) K b) =
      toPrincipalIdeal (𝓞 K) K (Units.map σ.toRingEquiv.toMonoidHom b) := by
    intro b
    rw [fractionalIdealUnitAction_principal,
      fractionField_ringOfIntegers_automorphism F K σ]
  have hσne : σ.toRingEquiv ≠ RingEquiv.refl K := by
    intro h
    apply hσ
    exact AlgEquiv.ext (RingEquiv.congr_fun h)
  obtain ⟨b, hb⟩ := RingEquiv.exists_invariant_of_involutive σ.toRingEquiv
    (quadratic_automorphism_involutive F K hd σ) hσne
    (fractionalIdealUnitAction (RingOfIntegers.mapAlgEquiv σ).toRingEquiv)
    (toPrincipalIdeal (𝓞 K) K) hcompat I (a / e)
    (by grind) hnorm'
  apply (mem_stronglyAmbiguousClassGroup F K σ _).mpr
  refine ⟨toPrincipalIdeal (𝓞 K) K b * I, hb, ?_⟩
  rw [map_mul, classGroup_mk_principal, one_mul]

/-- Equality of the concrete unit obstructions places the quotient of
two represented classes in the strongly ambiguous subgroup. -/
theorem equal_unit_obstructions_stronglyAmbiguous
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a b : Kˣ)
    (u v : (𝓞 F)ˣ)
    (hI : fractionalIdealUnitAction (K := K)
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv I = toPrincipalIdeal (𝓞 K) K a * I)
    (hJ : fractionalIdealUnitAction (K := K)
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv J = toPrincipalIdeal (𝓞 K) K b * J)
    (ha : Algebra.norm F (a : K) = ((u : 𝓞 F) : F))
    (hb : Algebra.norm F (b : K) = ((v : 𝓞 F) : F))
    (huv : QuotientGroup.mk (s := (relativeUnitNorm F K).range) u =
      QuotientGroup.mk v) :
    ClassGroup.mk K I / ClassGroup.mk K J ∈ stronglyAmbiguousClassGroup F K σ := by
  have huv' : u / v ∈ (relativeUnitNorm F K).range := by
    apply (QuotientGroup.eq_one_iff _).mp
    simp_all
  obtain ⟨w, hw⟩ := huv'
  have hnorm : Algebra.norm F ((a / b : Kˣ) : K) =
      Algebra.norm F (w : K) := by
    have hh := congrArg
      (fun z : (𝓞 F)ˣ => (Units.map (algebraMap (𝓞 F) F).toMonoidHom z : Fˣ)) hw
    rw [map_div] at hh
    have hh := congrArg (fun z : Fˣ => (z : F)) hh
    simp [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hh
    change Algebra.norm F (w : K) =
      ((u : 𝓞 F) : F) * (((v : 𝓞 F) : F))⁻¹ at hh
    simp [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      map_mul, Algebra.norm_inv]
    rw [ha, hb]
    exact hh.symm
  have hquot : fractionalIdealUnitAction
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv (I / J) =
      toPrincipalIdeal (𝓞 K) K (a / b) * (I / J) := by
    rw [map_div, hI, hJ, map_div]
    exact mul_div_mul_comm _ _ _ _
  simpa using exists_invariant_ideal_of_scalar_norm_unit
    F K hd σ hσ (I / J) (a / b) w hquot hnorm

