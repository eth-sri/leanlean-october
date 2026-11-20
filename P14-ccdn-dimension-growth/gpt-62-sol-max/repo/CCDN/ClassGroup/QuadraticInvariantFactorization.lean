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

omit [NumberField F] [FiniteDimensional F K] in
private lemma invariant_ideal_remainder
    (σ : K ≃ₐ[F] K) {I A R : Ideal (𝓞 K)}
    (hI : σ • I = I) (hA : σ • A = A) (hA0 : A ≠ 0)
    (he : I = A * R) : σ • R = R := by
  simp_all

/-- Every invariant integral ideal is an extended base ideal times a product of distinct
ramified primes. Remove a prime orbit, absorbing any repeated ramified factor in pairs. -/
theorem invariant_integral_ideal_ramified_factorization
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) (hinv : σ • I = I) :
    ∃ (J : Ideal (𝓞 F)) (t : Finset (Ideal (𝓞 K))),
      J ≠ 0 ∧ (∀ Q ∈ t, IsQuadraticRamifiedPrime F K Q) ∧
        I = J.map (algebraMap (𝓞 F) (𝓞 K)) * ∏ Q ∈ t, Q := by
  classical
  let extend := Ideal.map (algebraMap (𝓞 F) (𝓞 K))
  induction I using (wellFounded_dvdNotUnit (α := Ideal (𝓞 K))).induction with
  | h I ih =>
    by_cases hu : IsUnit I
    · exact ⟨1, ∅, one_ne_zero, by simp, by simp [Ideal.one_eq_top, Ideal.isUnit_iff.mp hu, Ideal.map_top]⟩
    obtain ⟨Q, hQir, R, hR⟩ := WfDvdMonoid.exists_irreducible_factor hu hI
    have hQ := UniqueFactorizationMonoid.irreducible_iff_prime.mp hQir
    let : Q.IsPrime := Ideal.isPrime_of_prime hQ
    let P := Q.under (𝓞 F)
    have hP := Ideal.under_ne_bot (𝓞 F) hQ.ne_zero
    have peel (A T : Ideal (𝓞 K)) (hA : σ • A = A) (hnu : ¬ IsUnit A) (he : I = A * T) := by
      have hT := right_ne_zero_of_mul (he ▸ hI)
      exact ih T ⟨hT, A, hnu, by rw [mul_comm, ← he]⟩ hT
        (invariant_ideal_remainder F K σ hinv hA (left_ne_zero_of_mul (he ▸ hI)) he)
    have absorb (A T : Ideal (𝓞 K)) (hA : σ • A = A) (hnu : ¬ IsUnit A)
        (he : I = A * T) (hm : extend P = A) :
        ∃ (J : Ideal (𝓞 F)) (t : Finset (Ideal (𝓞 K))),
          J ≠ 0 ∧ (∀ Q ∈ t, IsQuadraticRamifiedPrime F K Q) ∧
            I = extend J * ∏ Q ∈ t, Q := by
      obtain ⟨J, t, hJ, ht, hT⟩ := peel A T hA hnu he
      refine ⟨P * J, t, mul_ne_zero hP hJ, ht, ?_⟩
      rw [show extend (P * J) = extend P * extend J from Ideal.map_mul .., hm, he, hT, mul_assoc]
    have hmap := quadratic_prime_extension F K hd σ hσ Q hQ.ne_zero
    by_cases hf : σ • Q = Q
    · rw [ite_eq_left hf] at hmap
      rcases hmap with hmap | ⟨he, hmap⟩
      · exact absorb Q R hf hQir.not_isUnit hR hmap
      have hram : IsQuadraticRamifiedPrime F K Q := ⟨inferInstance, hQ.ne_zero, he⟩
      obtain ⟨J, t, hJ, ht, hT⟩ := peel Q R hf hQir.not_isUnit hR
      by_cases htQ : Q ∈ t
      · refine ⟨P * J, t.erase Q, mul_ne_zero hP hJ,
          fun A hA => ht A (Finset.mem_of_mem_erase hA), ?_⟩
        rw [hR, hT, Ideal.map_mul, hmap,
          ← Finset.mul_prod_erase t (fun Q => Q) htQ, pow_two]
        ac_rfl
      · refine ⟨J, insert Q t, hJ, ?_, ?_⟩
        · simpa [Finset.forall_mem_insert] using And.intro hram ht
        rw [hR, hT, Finset.prod_insert htQ]
        ac_rfl
    · have hg : Prime (σ • Q) := Ideal.prime_of_isPrime
        (by exact (smul_ne_zero_iff_ne σ).mpr hQ.ne_zero) inferInstance
      have hdvd : σ • Q ∣ I := ⟨σ • R, by rw [← smul_mul', ← hR, hinv]⟩
      rw [hR] at hdvd
      obtain ⟨T, hT⟩ := (hg.dvd_mul.mp hdvd).resolve_left
        (fun h => hf (associated_iff_eq.mp ((Prime.dvd_prime_iff_associated hg hQ).mp h)))
      have hσσ : σ * σ = 1 := AlgEquiv.ext (quadratic_automorphism_involutive F K hd σ)
      apply absorb (Q * (σ • Q)) T
      · rw [smul_mul', ← mul_smul, hσσ, one_smul, mul_comm]
      · exact fun h => hQir.not_isUnit (isUnit_of_mul_isUnit_left h)
      · rw [hR, hT, mul_assoc]
      · simpa only [ite_eq_right hf] using hmap

end
end CCDN
