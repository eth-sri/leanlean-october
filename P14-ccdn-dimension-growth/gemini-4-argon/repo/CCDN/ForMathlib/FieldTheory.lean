/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Counting monic divisors and intermediate fields; Hilbert 90 for an involution

Monic divisors of a nonzero polynomial are determined by their multisets of roots in an
algebraic closure, so there are at most `2 ^ natDegree` of them. Through a primitive element,
the intermediate fields of a finite separable extension inject into the monic divisors of a
minimal polynomial.

## Main results

* `Polynomial.card_monic_dvd_le_two_pow_natDegree`: a nonzero polynomial `f` over a field has at
  most `2 ^ f.natDegree` monic divisors.
* `IntermediateField.card_le_two_pow_finrank`: a finite separable extension `E / F` has at most
  `2 ^ finrank F E` intermediate fields.
* `RingEquiv.hilbert90_of_involutive`: Hilbert 90 for a nontrivial involution `σ` of a field,
  with an explicit construction that also works in characteristic two: if `a σ(a) = 1`, then
  `a σ(b) = b` for some `b ≠ 0`. `RingEquiv.hilbert90_units_of_involutive` is the unit-group form.
* `RingEquiv.exists_invariant_of_involutive`: for a compatible homomorphism `P` from the units,
  an element `I` with `τ I = P a * I` and `a σ(a) = 1` has a `τ`-invariant multiple `P b * I`.
-/

@[expose] public section

section

open Module Polynomial IntermediateField

namespace IntermediateField

/-- The number of intermediate fields depends only on the extension
degree, without a chosen normal closure or Galois-group estimate. -/
theorem card_le_two_pow_finrank
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    Nat.card (IntermediateField F E) ≤ 2 ^ Module.finrank F E := by
  /- A nonzero polynomial over a field has at most `2 ^ natDegree` monic divisors. -/
  classical
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  let f : E[X] := (minpoly F α).map (algebraMap F E)
  have hf : f ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero_of_finite F α)
  let L := AlgebraicClosure E
  let ι := algebraMap E L
  let P := ((f.map ι).roots.powerset).toFinset
  let g : IntermediateField F E → ↥P := fun K =>
    ⟨(((minpoly K α).map (algebraMap K E)).map ι).roots, by
      apply Multiset.mem_toFinset.mpr
      apply Multiset.mem_powerset.mpr
      apply Polynomial.roots.le_of_dvd (Polynomial.map_ne_zero hf)
      apply Polynomial.map_dvd ι
      convert Polynomial.map_dvd (algebraMap K E) (minpoly.dvd_map_of_isScalarTower F K α)
      rw [Polynomial.map_map]
      rfl⟩
  have hg : Function.Injective g := fun K K' heq => by
    have hmon (M : IntermediateField F E) : ((minpoly M α).map (algebraMap M E)).Monic :=
      (minpoly.monic (.of_finite M α)).map _
    have hr : (((minpoly K α).map (algebraMap K E)).map ι).roots =
        (((minpoly K' α).map (algebraMap K' E)).map ι).roots := congrArg Subtype.val heq
    have hp : (minpoly K α).map (algebraMap K E) = (minpoly K' α).map (algebraMap K' E) := by
      apply Polynomial.map_injective ι ι.injective
      rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic ((hmon K).map ι),
        (IsAlgClosed.splits _).eq_prod_roots_of_monic ((hmon K').map ι), hr]
    simpa only [adjoin_minpoly_coeff_of_exists_primitive_element F hα] using
      congrArg (fun p : E[X] => adjoin F (p.coeffs : Set E)) hp
  have hdeg : f.natDegree = Module.finrank F E :=
    (Polynomial.natDegree_map _).trans ((Field.primitive_element_iff_minpoly_natDegree_eq F α).mp hα)
  calc
    Nat.card (IntermediateField F E) ≤ Nat.card ↥P := Nat.card_le_card_of_injective g hg
    _ = P.card := by simp
    _ ≤ (f.map ι).roots.powerset.card := Multiset.toFinset_card_le _
    _ = 2 ^ (f.map ι).roots.card := Multiset.card_powerset _
    _ ≤ 2 ^ Module.finrank F E :=
      hdeg ▸ Nat.pow_le_pow_right (by omega) (Polynomial.card_roots_map_le_natDegree _)

end IntermediateField

end

namespace RingEquiv

variable {K : Type*} [Field K]

/-- If the scalar comparison of an element with its conjugate has norm
one, multiplication by a principal element produces an invariant
representative. Here the principal map is a homomorphism. -/
theorem exists_invariant_of_involutive
    {A : Type*} [CommGroup A]
    (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (hσne : σ ≠ RingEquiv.refl K) (τ : A →* A) (P : Kˣ →* A)
    (hcompat : ∀ b : Kˣ, τ (P b) = P (Units.map σ.toMonoidHom b))
    (I : A) (a : Kˣ) (hI : τ I = P a * I)
    (ha : (a : K) * σ (a : K) = 1) :
    ∃ b : Kˣ, τ (P b * I) = P b * I := by
  /- A norm-one scalar for a nontrivial involution is a multiplicative
  coboundary. The explicit construction also works in characteristic two. -/
  /- Hilbert 90 for a nontrivial involution, in the unit group: a unit `a` with
  `a σ(a) = 1` has the form `b / σ(b)` for some unit `b`. -/
  obtain ⟨b, hb, hab⟩ : ∃ b : K, b ≠ 0 ∧ (a : K) * σ b = b := by
    by_cases h : 1 + (a : K) = 0
    · have ha' : (a : K) = -1 := by linear_combination h
      obtain ⟨z, hz⟩ : ∃ z : K, σ z ≠ z := by
        by_contra! hn; exact hσne (RingEquiv.ext hn)
      refine ⟨z - σ z, sub_ne_zero.mpr hz.symm, ?_⟩
      rw [ha', map_sub]; change -1 * (σ z - σ (σ z)) = z - σ z; rw [hσ]; ring
    · exact ⟨1 + a, h, by rw [map_add, map_one, mul_add, mul_one, ha, add_comm]⟩
  have hb' : a * Units.map σ.toMonoidHom (Units.mk0 b hb) = Units.mk0 b hb := Units.ext hab
  refine ⟨Units.mk0 b hb, ?_⟩
  rw [map_mul, hcompat, hI, ← mul_assoc, mul_comm (P _), ← map_mul, hb']

end RingEquiv
