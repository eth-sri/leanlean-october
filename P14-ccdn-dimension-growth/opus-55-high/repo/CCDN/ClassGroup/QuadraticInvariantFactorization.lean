/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import CCDN.ClassGroup.QuadraticInvariantIdeals
import CCDN.ClassGroup.QuadraticNormConjugation

/-! Factorization of invariant integral ideals in a quadratic
extension. The only prime factors left after extending a base ideal are
ramified primes; repeated ramified factors can be absorbed in pairs. -/

namespace CCDN
open NumberField Ideal
open scoped Pointwise

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [FiniteDimensional F K]

/-- The predicate that `Q` is a nonzero prime ideal of `𝓞 K` with ramification index `2` over
`𝓞 F`. -/
def IsQuadraticRamifiedPrime (Q : Ideal (𝓞 K)) : Prop :=
  Q.IsPrime ∧ Q ≠ ⊥ ∧ Q.ramificationIdx (𝓞 F) = 2

section
variable (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) {Q : Ideal (𝓞 K)} (hQ : IsQuadraticRamifiedPrime F K Q)
include hd hσ hQ

theorem quadratic_ramified_prime_fixed
    :
    σ • Q = Q := by
  have : Q.IsPrime := hQ.1
  by_contra hm
  have hh := quadratic_moving_prime_unramified F K hd σ hσ Q hm
  have he := hQ.2.2
  omega

theorem quadratic_ramified_prime_square
    :
    Q ^ 2 = (Q.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 K)) := by
  have : Q.IsPrime := hQ.1
  have hh := quadratic_fixed_prime_extension F K hd σ hσ Q hQ.2.1
    (quadratic_ramified_prime_fixed F K hd σ hσ hQ)
  rw [hQ.2.2] at hh
  exact hh.symm

end

omit [NumberField F] [FiniteDimensional F K] in
lemma invariant_ideal_remainder
    (σ : K ≃ₐ[F] K) {I A R : Ideal (𝓞 K)}
    (hI : σ • I = I) (hA : σ • A = A) (hA0 : A ≠ 0)
    (he : I = A * R) : σ • R = R := by
  apply mul_left_cancel₀ hA0
  calc
    A * (σ • R) = σ • (A * R) := by simp_all
    _ = A * R := by grind

variable (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
include hd hσ

theorem invariant_integral_ideal_ramified_multiset
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) (hinv : σ • I = I) :
    ∃ (J : Ideal (𝓞 F)) (s : Multiset (Ideal (𝓞 K))),
      J ≠ 0 ∧ (∀ Q ∈ s, IsQuadraticRamifiedPrime F K Q) ∧
        I = J.map (algebraMap (𝓞 F) (𝓞 K)) * s.prod := by
  suffices ∀ I : Ideal (𝓞 K), I ≠ 0 → σ • I = I →
      ∃ (J : Ideal (𝓞 F)) (s : Multiset (Ideal (𝓞 K))),
        J ≠ 0 ∧ (∀ Q ∈ s, IsQuadraticRamifiedPrime F K Q) ∧
          I = J.map (algebraMap (𝓞 F) (𝓞 K)) * s.prod from this I hI hinv
  intro I
  induction I using (wellFounded_dvdNotUnit (α := Ideal (𝓞 K))).induction with
  | h I ih =>
    intro hI hinv
    by_cases hu : IsUnit I
    · have htop : I = 1 := by simpa using Ideal.isUnit_iff.mp hu
      refine ⟨1, 0, one_ne_zero, by simp, ?_⟩
      rw [htop, Multiset.prod_zero, mul_one]
      simpa using (Ideal.map_top (algebraMap (𝓞 F) (𝓞 K))).symm
    obtain ⟨Q, hQir, hQdiv⟩ := WfDvdMonoid.exists_irreducible_factor hu hI
    have hQprime := UniqueFactorizationMonoid.irreducible_iff_prime.mp hQir
    have : Q.IsPrime := Ideal.isPrime_of_prime hQprime
    have hQ0 := hQprime.ne_zero
    have hp0 := Ideal.under_ne_bot (𝓞 F) hQ0
    obtain ⟨R, hR⟩ := hQdiv
    by_cases hfix : σ • Q = Q
    · have hR0 : R ≠ 0 := by intro hz; simp [hz] at hR; exact hI hR
      have hRinv := invariant_ideal_remainder F K σ hinv hfix hQ0 hR
      obtain ⟨J, s, hJ, hs, hJs⟩ := ih R (⟨hR0, Q, hQir.not_isUnit, by grind⟩) hR0 hRinv
      rcases quadratic_prime_ramification_one_or_two F K hd Q with he | he
      · have hmap := quadratic_fixed_prime_extension F K hd σ hσ Q hQ0 hfix
        rw [he, pow_one] at hmap
        refine ⟨Q.under (𝓞 F) * J, s, mul_ne_zero hp0 hJ, hs, ?_⟩
        rw [Ideal.map_mul, hmap, hR, hJs]
        ac_rfl
      · refine ⟨J, Q ::ₘ s, hJ, ?_, ?_⟩
        · intro P hP
          rcases Multiset.mem_cons.mp hP with rfl | hP
          · exact ⟨inferInstance, hQ0, he⟩
          grind
        · rw [Multiset.prod_cons, hR, hJs]
          ac_rfl
    · have hσQprime : Prime (σ • Q) := Ideal.prime_of_isPrime
        (by
          intro hz
          have hh := congrArg (fun A ↦ σ⁻¹ • A) hz
          apply hQ0
          simpa using hh) inferInstance
      have hσQdiv : σ • Q ∣ I := by
        refine ⟨σ • R, ?_⟩
        simp_all
      obtain ⟨T, hT⟩ := (by
        rw [hR] at hσQdiv
        exact (hσQprime.dvd_mul.mp hσQdiv).resolve_left (by
          intro hh
          have he := (Prime.dvd_prime_iff_associated hσQprime hQprime).mp hh
          exact hfix (associated_iff_eq.mp he)))
      have hIeq : I = (Q * (σ • Q)) * T := by rw [hR, hT]; ac_rfl
      have hA0 := mul_ne_zero hQ0 hσQprime.ne_zero
      have hT0 : T ≠ 0 := by grind
      have hσσ : σ * σ = 1 := AlgEquiv.ext (quadratic_automorphism_involutive F K hd σ)
      have hTinv := invariant_ideal_remainder F K σ hinv (by
        rw [smul_mul', ← mul_smul, hσσ, one_smul, mul_comm]) hA0 hIeq
      have hAnu : ¬ IsUnit (Q * (σ • Q)) := by
        intro hu
        exact hQir.not_isUnit (isUnit_of_mul_isUnit_left hu)
      have hTDvd : DvdNotUnit T I :=
        ⟨hT0, Q * (σ • Q), hAnu, by simpa [mul_comm] using hIeq⟩
      obtain ⟨J, s, hJ, hs, hJs⟩ := ih T hTDvd hT0 hTinv
      refine ⟨Q.under (𝓞 F) * J, s, mul_ne_zero hp0 hJ, hs, ?_⟩
      rw [Ideal.map_mul, quadratic_moving_prime_extension F K hd σ hσ Q hQ0 hfix,
        hIeq, hJs]
      ac_rfl

theorem quadratic_ramified_multiset_parity
    (s : Multiset (Ideal (𝓞 K)))
    (hs : ∀ Q ∈ s, IsQuadraticRamifiedPrime F K Q) :
    ∃ (J : Ideal (𝓞 F)) (t : Finset (Ideal (𝓞 K))),
      J ≠ 0 ∧ (∀ Q ∈ t, IsQuadraticRamifiedPrime F K Q) ∧
        s.prod = J.map (algebraMap (𝓞 F) (𝓞 K)) * ∏ Q ∈ t, Q := by
  induction s using Multiset.induction_on with
  | empty =>
    refine ⟨1, ∅, one_ne_zero, by simp, ?_⟩
    simp
    simpa using (Ideal.map_top (algebraMap (𝓞 F) (𝓞 K))).symm
  | cons Q s ih =>
    have hQ := hs Q (Multiset.mem_cons_self Q s)
    obtain ⟨J, t, hJ, ht, he⟩ := ih (fun P hP ↦ hs P (Multiset.mem_cons_of_mem hP))
    by_cases hQt : Q ∈ t
    · have hp0 := Ideal.under_ne_bot (𝓞 F) hQ.2.1
      refine ⟨Q.under (𝓞 F) * J, t.erase Q, mul_ne_zero hp0 hJ,
        fun P hP ↦ ht P (Finset.mem_of_mem_erase hP), ?_⟩
      have hprod :=
        Finset.mul_prod_erase t (fun P ↦ P) hQt
      rw [Multiset.prod_cons, he, Ideal.map_mul,
        ← quadratic_ramified_prime_square F K hd σ hσ hQ, ← hprod, pow_two]
      ac_rfl
    · refine ⟨J, insert Q t, hJ, ?_, ?_⟩
      · grind
      · rw [Multiset.prod_cons, he, Finset.prod_insert hQt]
        ac_rfl

/-- Every invariant integral ideal is an extended base ideal times a
product of distinct ramified prime ideals. -/
theorem invariant_integral_ideal_ramified_factorization
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) (hinv : σ • I = I) :
    ∃ (J : Ideal (𝓞 F)) (t : Finset (Ideal (𝓞 K))),
      J ≠ 0 ∧ (∀ Q ∈ t, IsQuadraticRamifiedPrime F K Q) ∧
        I = J.map (algebraMap (𝓞 F) (𝓞 K)) * ∏ Q ∈ t, Q := by
  obtain ⟨J, s, hJ, hs, hIeq⟩ :=
    invariant_integral_ideal_ramified_multiset F K hd σ hσ I hI hinv
  obtain ⟨J', t, hJ', ht, hsprod⟩ := quadratic_ramified_multiset_parity F K hd σ hσ s hs
  refine ⟨J * J', t, mul_ne_zero hJ hJ', ht, ?_⟩
  rw [hIeq, hsprod, Ideal.map_mul]
  ac_rfl

