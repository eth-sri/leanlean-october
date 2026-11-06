/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.QuadraticAmbiguousClassBound
public import CCDN.ClassGroup.QuadraticInvariantFactorization
import CCDN.ClassGroup.DiscriminantPrimeIdealCover
import CCDN.ClassGroup.InvariantIdealIntegralRepresentative
import CCDN.ClassGroup.QuadraticInvariantIdeals
import CCDN.ClassGroup.QuadraticNormConjugation
import CCDN.ForMathlib.FiniteGroupPowerTorsion

/-!
The two-torsion in the strongly ambiguous class group is
bounded by base-field two-torsion and the finite set of ramified primes.
The cover comes from the proved invariant-ideal factorization.

Ideal-class notation for finite products of nonzero integral ideals.
The value at the zero ideal is set to one only to make the indexing
function total; multiplicativity below explicitly requires nonzero ideals.
-/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped Pointwise nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The ideal class of an integral ideal, with the zero ideal sent to the trivial class. -/
def integralIdealClass (I : Ideal R) : ClassGroup R :=
  if h : I = 0 then 1 else ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr h⟩

private lemma integralIdealClass_eq (I : Ideal R) (hI : I ≠ 0) :
    integralIdealClass I = ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ := by
  simp only [integralIdealClass, dite_eq_right hI]

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [FiniteDimensional F K]

/-- A fully constructed discriminant-prime cover gives the
strongly ambiguous two-torsion estimate. -/
theorem stronglyAmbiguousTwoTorsion_card_le_discriminant_primes
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) :
    Nat.card (stronglyAmbiguousTwoTorsion F K σ) ≤
      classGroupTwoTorsionCard F *
        2 ^ (Module.finrank ℚ K * (NumberField.discr K).natAbs.primeFactors.card) := by
  have hmul {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0) :
      integralIdealClass (I * J) = integralIdealClass I * integralIdealClass J := by
    rw [integralIdealClass_eq _ (mul_ne_zero hI hJ),
      integralIdealClass_eq _ hI, integralIdealClass_eq _ hJ]
    exact map_mul (ClassGroup.mk0 (R := 𝓞 K))
      (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ : (Ideal (𝓞 K))⁰)
      (⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩ : (Ideal (𝓞 K))⁰)
  have hprod (s : Finset (Ideal (𝓞 K))) (hs : ∀ I ∈ s, I ≠ 0) :
      integralIdealClass (∏ I ∈ s, I) = ∏ I ∈ s, integralIdealClass I := by
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.prod_empty, integralIdealClass_eq _ one_ne_zero]
      exact map_one ClassGroup.mk0
    | @insert I s hIs ih =>
      have hs' : ∀ J ∈ s, J ≠ 0 := fun J hJ => hs J (Finset.mem_insert_of_mem hJ)
      rw [Finset.prod_insert hIs, hmul (hs I (Finset.mem_insert_self I s))
        (Finset.prod_ne_zero_iff.mpr hs'), ih hs', Finset.prod_insert hIs]
  let S := discriminantPrimeIdealCover K
  have hcover (c : stronglyAmbiguousClassGroup F K σ) :
      ∃ a : ClassGroup (𝓞 F), ∃ t : S.powerset,
        c.val = ClassGroup.extendedHom (𝓞 F) (𝓞 K) a * ∏ Q ∈ t.val, integralIdealClass Q := by
    obtain ⟨J, hJ, hJc⟩ := (mem_stronglyAmbiguousClassGroup F K σ c.val).mp c.property
    obtain ⟨I, hIinv, hIc⟩ := exists_invariant_integral_ideal_representative
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
      (fun x => RingOfIntegers.ext (quadratic_automorphism_involutive F K hd σ (x : K))) J hJ
    have hI0 : (I : Ideal (𝓞 K)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.property
    have hc : integralIdealClass (I : Ideal (𝓞 K)) = c.val :=
      (integralIdealClass_eq _ hI0).trans (hIc.trans hJc)
    obtain ⟨A, t, hA, ht, hfact⟩ := invariant_integral_ideal_ramified_factorization F K hd σ hσ I
      hI0 (by rwa [quadratic_integer_ideal_action])
    have htS : t ⊆ S := fun Q hQ => by
      have : Q.IsPrime := (ht Q hQ).1
      exact mem_discriminantPrimeIdealCover_of_ramification_two K F Q (ht Q hQ).2.1 (ht Q hQ).2.2
    have ht0 : ∀ Q ∈ t, Q ≠ 0 := fun Q hQ => (ht Q hQ).2.1
    refine ⟨integralIdealClass A, ⟨t, Finset.mem_powerset.mpr htS⟩, ?_⟩
    rw [← hc, hfact, hmul (Ideal.map_ne_bot_of_ne_bot hA)
        (Finset.prod_ne_zero_iff.mpr ht0), hprod t ht0,
      integralIdealClass_eq A hA, ClassGroup.extendedHom_mk0]
    congr 1
    exact integralIdealClass_eq _ (mem_nonZeroDivisors_iff_ne_zero.mp
      (ClassGroup.extendedIdeal (𝓞 F) (𝓞 K) ⟨A, mem_nonZeroDivisors_iff_ne_zero.mpr hA⟩).property)
  have hh : Nat.card (stronglyAmbiguousTwoTorsion F K σ) ≤
      classGroupTwoTorsionCard F * 2 ^ S.card := by
    simpa only [Fintype.card_coe, Finset.card_powerset, stronglyAmbiguousTwoTorsion,
      classGroupTwoTorsionCard, classGroupTwoTorsion] using
      MonoidHom.card_powMonoidHom_ker_le_of_coset_cover
        (ClassGroup.extendedHom (𝓞 F) (𝓞 K)) (stronglyAmbiguousClassGroup F K σ)
        (fun t : S.powerset => ∏ Q ∈ t.val, integralIdealClass Q) hcover 2
  exact hh.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) (discriminantPrimeIdealCover_card_le K)))

end
end CCDN
