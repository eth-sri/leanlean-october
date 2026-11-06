/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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
open scoped NumberField nonZeroDivisors

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-- The relative norm `N_{K/F}` restricted to unit groups of rings of integers. -/
def relativeUnitNorm : (𝓞 K)ˣ →* (𝓞 F)ˣ :=
  Units.map (RingOfIntegers.norm F)

/-- The unit-norm obstruction group: the units of `𝓞 F` modulo the relative norms of units of
`𝓞 K`. -/
abbrev quadraticUnitNormQuotient :=
  (𝓞 F)ˣ ⧸ (relativeUnitNorm F K).range

private theorem quadraticUnitNormQuotient_square (hd : Module.finrank F K = 2)
    (x : quadraticUnitNormQuotient F K) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom u,
      hd ▸ Units.ext (RingOfIntegers.norm_algebraMap F u)⟩

variable [NumberField F]

/-- For a quadratic extension `K / F` of number fields, the unit-norm quotient is finite. -/
theorem quadraticUnitNormQuotient_finite (hd : Module.finrank F K = 2) :
    Finite (quadraticUnitNormQuotient F K) :=
  (numberFieldUnit_exponent_two_quotient F
    (QuotientGroup.mk' (relativeUnitNorm F K).range)
    (QuotientGroup.mk'_surjective _) (quadraticUnitNormQuotient_square F K hd)).1

/-- For a quadratic extension `K / F` of number fields, the unit-norm quotient has order at most
`2 ^ [F : ℚ]`. -/
theorem quadraticUnitNormQuotient_card_le_degree (hd : Module.finrank F K = 2) :
    Nat.card (quadraticUnitNormQuotient F K) ≤ 2 ^ Module.finrank ℚ F :=
  (numberFieldUnit_exponent_two_quotient F
    (QuotientGroup.mk' (relativeUnitNorm F K).range)
    (QuotientGroup.mk'_surjective _) (quadraticUnitNormQuotient_square F K hd)).2.trans
    (Nat.pow_le_pow_right (by norm_num) (numberField_unit_rank_add_one_le_degree F))

variable [NumberField K]

/-- Classes represented by invariant invertible fractional ideals. -/
def stronglyAmbiguousClassGroup (σ : K ≃ₐ[F] K) : Subgroup (ClassGroup (𝓞 K)) :=
  ((ClassGroup.mk K).comp
    ((fractionalIdealUnitAction (K := K)
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv).eqLocus
        (MonoidHom.id _)).subtype).range

omit [NumberField F] in
/-- An ideal class is strongly ambiguous if and only if it is the class of a `σ`-invariant
invertible fractional ideal. -/
theorem mem_stronglyAmbiguousClassGroup (σ : K ≃ₐ[F] K) (c : ClassGroup (𝓞 K)) :
    c ∈ stronglyAmbiguousClassGroup F K σ ↔
      ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
        fractionalIdealUnitAction (K := K)
          (RingOfIntegers.mapAlgEquiv σ).toRingEquiv I = I ∧ ClassGroup.mk K I = c :=
  ⟨fun ⟨I, hI⟩ => ⟨I, I.property, hI⟩, fun ⟨I, hI, hc⟩ => ⟨⟨I, hI⟩, hc⟩⟩

/-- Equality of the concrete unit obstructions places the quotient of
two represented classes in the strongly ambiguous subgroup. -/
theorem equal_unit_obstructions_stronglyAmbiguous
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
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
  obtain ⟨w, hw⟩ : u / v ∈ (relativeUnitNorm F K).range := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_div, huv, div_self']
  let e : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom w
  let ab : Kˣ := a / b
  let c : Kˣ := ab / e
  have hpe : toPrincipalIdeal (𝓞 K) K e = 1 := Units.ext <| by
    simp only [coe_toPrincipalIdeal, Units.val_one]
    change FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K (w : 𝓞 K)) = 1
    rw [← FractionalIdeal.coeIdeal_span_singleton (S := (𝓞 K)⁰) (P := K)]
    simp only [Ideal.span_singleton_eq_top.mpr w.isUnit, FractionalIdeal.coeIdeal_top]
  have hnorm_ab : Algebra.norm F (ab : K) = Algebra.norm F ((w : 𝓞 K) : K) := by
    have hh := congrArg (fun z : Fˣ => (z : F)) (congrArg
      (fun z : (𝓞 F)ˣ => (Units.map (algebraMap (𝓞 F) F).toMonoidHom z : Fˣ)) hw)
    rw [map_div] at hh
    simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hh
    change Algebra.norm F ((w : 𝓞 K) : K) = ((u : 𝓞 F) : F) * (((v : 𝓞 F) : F))⁻¹ at hh
    simp only [ab, div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, Algebra.norm_inv]
    rw [ha, hb, hh]
  have hnorm : Algebra.norm F (c : K) = 1 := by
    simp only [c, div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, Algebra.norm_inv]
    change Algebra.norm F (ab : K) * (Algebra.norm F ((w : 𝓞 K) : K))⁻¹ = 1
    rw [hnorm_ab, mul_inv_cancel₀
      (Algebra.norm_ne_zero_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr w.ne_zero))]
  have hnorm' : (c : K) * σ (c : K) = 1 := by
    rw [← quadratic_norm_eq_mul_conjugate F K hd σ hσ, hnorm, map_one]
  have hff : (IsFractionRing.ringEquivOfRingEquiv
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv : K ≃+* K) = σ.toRingEquiv := by
    apply RingEquiv.ext
    have h : (IsFractionRing.ringEquivOfRingEquiv
        (RingOfIntegers.mapAlgEquiv σ).toRingEquiv : K ≃+* K).toRingHom = σ.toRingHom :=
      IsFractionRing.ringHom_ext (A := 𝓞 K) fun x =>
        IsFractionRing.ringEquivOfRingEquiv_algebraMap (RingOfIntegers.mapAlgEquiv σ).toRingEquiv x
    exact RingHom.congr_fun h
  have hcompat (x : Kˣ) :
      fractionalIdealUnitAction (K := K) (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
        (toPrincipalIdeal (𝓞 K) K x) =
      toPrincipalIdeal (𝓞 K) K (Units.map σ.toRingEquiv.toMonoidHom x) := by
    rw [fractionalIdealUnitAction_principal, hff]
  have hquot : fractionalIdealUnitAction (K := K)
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv (I / J) =
      toPrincipalIdeal (𝓞 K) K c * (I / J) := by
    rw [show toPrincipalIdeal (𝓞 K) K c = toPrincipalIdeal (𝓞 K) K (a / b) by
      dsimp only [c]; rw [map_div, hpe, div_one], map_div, hI, hJ, map_div, mul_div_mul_comm]
  obtain ⟨d, hd'⟩ := RingEquiv.exists_invariant_of_involutive σ.toRingEquiv
    (quadratic_automorphism_involutive F K hd σ)
    (fun h => hσ (AlgEquiv.ext (RingEquiv.congr_fun h)))
    (fractionalIdealUnitAction (K := K) (RingOfIntegers.mapAlgEquiv σ).toRingEquiv)
    (toPrincipalIdeal (𝓞 K) K) hcompat (I / J) c hquot hnorm'
  rw [← map_div, mem_stronglyAmbiguousClassGroup]
  exact ⟨toPrincipalIdeal (𝓞 K) K d * (I / J), hd', by rw [map_mul, classGroup_mk_principal, one_mul]⟩

end
end CCDN
