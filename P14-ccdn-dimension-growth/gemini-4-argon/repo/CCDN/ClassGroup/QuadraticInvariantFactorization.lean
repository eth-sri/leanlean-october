/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
import CCDN.ClassGroup.QuadraticInvariantIdeals
import CCDN.ClassGroup.QuadraticNormConjugation

/-! Factorization of invariant integral ideals in a quadratic
extension. The only prime factors left after extending a base ideal are
ramified primes; repeated ramified factors can be absorbed in pairs. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField Ideal
open scoped Pointwise

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [FiniteDimensional F K]

/-- The predicate that `Q` is a nonzero prime ideal of `𝓞 K` with ramification index `2` over
`𝓞 F`. -/
def IsQuadraticRamifiedPrime (Q : Ideal (𝓞 K)) : Prop :=
  Q.IsPrime ∧ Q ≠ ⊥ ∧ Q.ramificationIdx (𝓞 F) = 2

/-- Every invariant integral ideal is an extended base ideal times a
product of distinct ramified prime ideals. -/
theorem invariant_integral_ideal_ramified_factorization
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) (hinv : σ • I = I) :
    ∃ (J : Ideal (𝓞 F)) (t : Finset (Ideal (𝓞 K))),
      J ≠ 0 ∧ (∀ Q ∈ t, IsQuadraticRamifiedPrime F K Q) ∧
        I = J.map (algebraMap (𝓞 F) (𝓞 K)) * ∏ Q ∈ t, Q := by
  have hrem {I₀ A R : Ideal (𝓞 K)} (hI₀ : σ • I₀ = I₀) (hA : σ • A = A)
      (hA0 : A ≠ 0) (he : I₀ = A * R) : σ • R = R :=
    mul_left_cancel₀ hA0 <| calc
      A * (σ • R) = σ • (A * R) := by rw [smul_mul', hA]
      _ = A * R := by rw [← he, hI₀, he]
  have hmult : ∀ I : Ideal (𝓞 K), I ≠ 0 → σ • I = I →
      ∃ (J : Ideal (𝓞 F)) (s : Multiset (Ideal (𝓞 K))),
        J ≠ 0 ∧ (∀ Q ∈ s, IsQuadraticRamifiedPrime F K Q) ∧
          I = J.map (algebraMap (𝓞 F) (𝓞 K)) * s.prod := by
    intro I
    induction I using (wellFounded_dvdNotUnit (α := Ideal (𝓞 K))).induction with
    | h I ih =>
      intro hI hinv
      by_cases hu : IsUnit I
      · refine ⟨1, 0, one_ne_zero, by simp, ?_⟩
        rw [show I = 1 by simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp hu,
          Multiset.prod_zero, mul_one]
        simpa only [Ideal.one_eq_top] using (Ideal.map_top (algebraMap (𝓞 F) (𝓞 K))).symm
      obtain ⟨Q, hQir, R, hR⟩ := WfDvdMonoid.exists_irreducible_factor hu hI
      have hQprime : Prime Q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hQir
      have : Q.IsPrime := Ideal.isPrime_of_prime hQprime
      have hQ0 : Q ≠ 0 := hQprime.ne_zero
      have hp0 : Q.under (𝓞 F) ≠ 0 := Ideal.under_ne_bot (𝓞 F) hQ0
      by_cases hfix : σ • Q = Q
      · have hR0 : R ≠ 0 := fun hz => hI (by simp [hz] at hR; exact hR)
        obtain ⟨J, s, hJ, hs, hJs⟩ := ih R
          ⟨hR0, Q, hQir.not_isUnit, by simpa [mul_comm] using hR⟩ hR0 (hrem hinv hfix hQ0 hR)
        rcases quadratic_prime_ramification_one_or_two F K hd Q with he | he
        · have hmap := quadratic_fixed_prime_extension F K hd σ hσ Q hQ0 hfix
          rw [he, pow_one] at hmap
          refine ⟨Q.under (𝓞 F) * J, s, mul_ne_zero hp0 hJ, hs, ?_⟩
          rw [Ideal.map_mul, hmap, hR, hJs]; ac_rfl
        · refine ⟨J, Q ::ₘ s, hJ, fun P hP => ?_, ?_⟩
          · rcases Multiset.mem_cons.mp hP with rfl | hP
            · exact ⟨inferInstance, hQ0, he⟩
            · exact hs P hP
          · rw [Multiset.prod_cons, hR, hJs]; ac_rfl
      · have hσQprime : Prime (σ • Q) := Ideal.prime_of_isPrime
          (fun hz => hQ0 (by
            simpa only [inv_smul_smul, show (⊥ : Ideal (𝓞 K)) = 0 from rfl, smul_zero] using
              congrArg (fun A : Ideal (𝓞 K) ↦ σ⁻¹ • A) hz)) inferInstance
        have hσQdiv : σ • Q ∣ I := ⟨σ • R, by rw [← smul_mul', ← hR, hinv]⟩
        rw [hR] at hσQdiv
        obtain ⟨T, hT⟩ := (hσQprime.dvd_mul.mp hσQdiv).resolve_left fun hh =>
          hfix (associated_iff_eq.mp ((Prime.dvd_prime_iff_associated hσQprime hQprime).mp hh))
        have hIeq : I = (Q * (σ • Q)) * T := by rw [hR, hT]; ac_rfl
        have hT0 : T ≠ 0 := fun hz => hI (by simp [hz] at hIeq; exact hIeq)
        have hσσ : σ * σ = 1 := AlgEquiv.ext (quadratic_automorphism_involutive F K hd σ)
        have hAinv : σ • (Q * (σ • Q)) = Q * (σ • Q) := by
          rw [smul_mul', ← mul_smul, hσσ, one_smul, mul_comm]
        obtain ⟨J, s, hJ, hs, hJs⟩ := ih T
          ⟨hT0, Q * (σ • Q), fun hu => hQir.not_isUnit (isUnit_of_mul_isUnit_left hu),
            by simpa [mul_comm] using hIeq⟩ hT0
          (hrem hinv hAinv (mul_ne_zero hQ0 hσQprime.ne_zero) hIeq)
        refine ⟨Q.under (𝓞 F) * J, s, mul_ne_zero hp0 hJ, hs, ?_⟩
        rw [Ideal.map_mul, quadratic_moving_prime_extension F K hd σ hσ Q hQ0 hfix, hIeq, hJs]
        ac_rfl
  obtain ⟨J, s, hJ, hs, hIeq⟩ := hmult I hI hinv
  have hpar : ∀ s : Multiset (Ideal (𝓞 K)), (∀ Q ∈ s, IsQuadraticRamifiedPrime F K Q) →
      ∃ (J' : Ideal (𝓞 F)) (t : Finset (Ideal (𝓞 K))),
        J' ≠ 0 ∧ (∀ Q ∈ t, IsQuadraticRamifiedPrime F K Q) ∧
          s.prod = J'.map (algebraMap (𝓞 F) (𝓞 K)) * ∏ Q ∈ t, Q := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      intro _
      refine ⟨1, ∅, one_ne_zero, by simp, ?_⟩
      simp only [Multiset.prod_zero, Finset.prod_empty, mul_one]
      simpa only [Ideal.one_eq_top] using (Ideal.map_top (algebraMap (𝓞 F) (𝓞 K))).symm
    | cons Q s ih =>
      intro hs
      have hQ := hs Q (Multiset.mem_cons_self Q s)
      obtain ⟨J', t, hJ', ht, he⟩ := ih fun P hP ↦ hs P (Multiset.mem_cons_of_mem hP)
      by_cases hQt : Q ∈ t
      · refine ⟨Q.under (𝓞 F) * J', t.erase Q,
          mul_ne_zero (Ideal.under_ne_bot (𝓞 F) hQ.2.1) hJ',
          fun P hP ↦ ht P (Finset.mem_of_mem_erase hP), ?_⟩
        have : Q.IsPrime := hQ.1
        have hfix : σ • Q = Q := by
          by_contra hm
          have := quadratic_moving_prime_unramified F K hd σ hσ Q hm
          have := hQ.2.2; omega
        have hsq := quadratic_fixed_prime_extension F K hd σ hσ Q hQ.2.1 hfix
        rw [hQ.2.2] at hsq
        rw [Multiset.prod_cons, he, Ideal.map_mul, hsq,
          ← Finset.mul_prod_erase t (fun P ↦ P) hQt, pow_two]
        ac_rfl
      · refine ⟨J', insert Q t, hJ', fun P hP => ?_, ?_⟩
        · rcases Finset.mem_insert.mp hP with rfl | hP
          · exact hQ
          · exact ht P hP
        · rw [Multiset.prod_cons, he, Finset.prod_insert hQt]; ac_rfl
  obtain ⟨J', t, hJ', ht, hsprod⟩ := hpar s hs
  refine ⟨J * J', t, mul_ne_zero hJ hJ', ht, ?_⟩
  rw [hIeq, hsprod, Ideal.map_mul]; ac_rfl

end
end CCDN
