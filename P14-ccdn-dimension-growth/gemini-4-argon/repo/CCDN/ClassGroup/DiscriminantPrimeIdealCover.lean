/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! A finite, coefficient-free cover of the finite prime ideals that
can ramify in a subextension of a number field. The cover is constructed
from rational primes dividing the absolute discriminant, and its size
is bounded by the field degree times their number. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/- The finite set of prime ideals of `𝓞 K` lying over the rational prime ideal `(p)`. -/

/-- The finite set of prime ideals of `𝓞 K` lying over rational primes dividing the absolute
discriminant of `K`; it contains every nonzero prime that ramifies in some subextension. -/
def discriminantPrimeIdealCover : Finset (Ideal (𝓞 K)) :=
  (NumberField.discr K).natAbs.primeFactors.biUnion fun p =>
    (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K) (Ideal.span {(p : ℤ)})).toFinset

/-- The discriminant prime-ideal cover has at most `[K : ℚ]` times the number of prime factors of
the absolute discriminant. -/
theorem discriminantPrimeIdealCover_card_le :
    (discriminantPrimeIdealCover K).card ≤
      Module.finrank ℚ K * (NumberField.discr K).natAbs.primeFactors.card := by
  calc
    _ ≤ ∑ p ∈ (NumberField.discr K).natAbs.primeFactors,
        (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K)
          (Ideal.span {(p : ℤ)})).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ (NumberField.discr K).natAbs.primeFactors,
        Module.finrank ℚ K := Finset.sum_le_sum fun p hp => by
          have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Nat.prime_of_mem_primeFactors hp)
          let P : Ideal ℤ := Ideal.span {(p : ℤ)}
          have : P.IsPrime := (Ideal.span_singleton_prime hpz.ne_zero).mpr hpz
          let : Fintype (P.primesOver (𝓞 K)) :=
            (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K) P).fintype
          have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 K)
          rw [RingOfIntegers.rank] at hsum
          rw [Set.Finite.card_toFinset _, ← hsum]
          refine (by simp : Fintype.card (P.primesOver (𝓞 K)) = ∑ _Q : P.primesOver (𝓞 K), 1).trans_le
            (Finset.sum_le_sum fun Q _ => ?_)
          have : Q.val.IsPrime := Q.property.1
          exact Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_pos (Q.val.ramificationIdx_pos ℤ) (Q.val.inertiaDeg_pos ℤ)).ne'
    _ = _ := by simp [Nat.mul_comm]

variable (F : Type*) [Field F] [NumberField F] [Algebra F K]

/-- For a quadratic extension `K / F` of number fields, `|discr F| ^ 2 ≤ |discr K|`. -/
theorem quadratic_absolute_discriminant_square_le (hd : Module.finrank F K = 2) :
    (NumberField.discr F).natAbs ^ 2 ≤ (NumberField.discr K).natAbs := by
  /- Discriminant descent in its exact extension-degree form. -/
  rw [← hd]
  refine Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))
    ⟨Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 K)), ?_⟩
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) K (𝓞 K),
    Nat.mul_comm]

/-- Relative ramification index two forces the prime into the
finite discriminant cover. -/
theorem mem_discriminantPrimeIdealCover_of_ramification_two
    (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (he : Q.ramificationIdx (𝓞 F) = 2) :
    Q ∈ discriminantPrimeIdealCover K := by
  have : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
  obtain ⟨p, _, _, hpQ, hp, _⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdiv : (p : ℤ) ∣ NumberField.discr K := by
    by_contra h
    have : Algebra.IsUnramifiedAt ℤ Q :=
      (NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) hpz).mp h
        Q inferInstance (by simpa only [Int.cast_natCast] using hpQ)
    have hdvd : Q.ramificationIdx (𝓞 F) ∣ Q.ramificationIdx ℤ :=
      Ideal.ramificationIdx_above_dvd (R := ℤ) (Q.under (𝓞 F)) Q
    rw [he, Q.ramificationIdx_eq_one ℤ] at hdvd
    norm_num at hdvd
  have hpf : p ∈ (NumberField.discr K).natAbs.primeFactors :=
    hp.mem_primeFactors (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdiv)
      (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K))
  refine Finset.mem_biUnion.mpr ⟨p, hpf, (Set.Finite.mem_toFinset _).mpr ⟨inferInstance, ?_⟩⟩
  exact (Ideal.liesOver_span_iff (inferInstance : Q.IsPrime).ne_top hpz).mpr
    (by simpa only [map_natCast] using hpQ)

end
end CCDN
