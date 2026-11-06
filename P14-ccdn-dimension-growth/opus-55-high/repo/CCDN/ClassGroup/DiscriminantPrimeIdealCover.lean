/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! A finite, coefficient-free cover of the finite prime ideals that
can ramify in a subextension of a number field. The cover is constructed
from rational primes dividing the absolute discriminant, and its size
is bounded by the field degree times their number. -/

namespace CCDN
noncomputable section
open NumberField
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

section
variable (p : ℕ)

/-- The finite set of prime ideals of `𝓞 K` lying over the rational prime ideal `(p)`. -/
def rationalPrimeIdealFiber : Finset (Ideal (𝓞 K)) :=
  (Algebra.QuasiFinite.finite_primesOver
    (S := 𝓞 K) (Ideal.span {(p : ℤ)})).toFinset

theorem rationalPrimeIdealFiber_card_le (hp : p.Prime) :
    (rationalPrimeIdealFiber K p).card ≤ Module.finrank ℚ K := by
  have hpz := Nat.prime_iff_prime_int.mp hp
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have : P.IsPrime := (Ideal.span_singleton_prime hpz.ne_zero).mpr hpz
  let : Fintype (P.primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver P).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 K)
  rw [RingOfIntegers.rank] at hsum
  have hcard : (rationalPrimeIdealFiber K p).card =
      Fintype.card (P.primesOver (𝓞 K)) :=
    Set.Finite.card_toFinset _
  rw [hcard, ← hsum]
  calc
    _ = ∑ _Q : P.primesOver (𝓞 K), 1 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro Q _
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_pos (Q.val.ramificationIdx_pos ℤ) (Q.val.inertiaDeg_pos ℤ)).ne'

end

/-- The finite set of prime ideals of `𝓞 K` lying over rational primes dividing the absolute
discriminant of `K`; it contains every nonzero prime that ramifies in some subextension. -/
def discriminantPrimeIdealCover : Finset (Ideal (𝓞 K)) :=
  (NumberField.discr K).natAbs.primeFactors.biUnion (rationalPrimeIdealFiber K)

variable (F : Type*) [Field F] [NumberField F] [Algebra F K]

/-- Discriminant descent in its exact extension-degree form. -/
theorem absolute_discriminant_power_le :
    (NumberField.discr F).natAbs ^ Module.finrank F K ≤
      (NumberField.discr K).natAbs := by
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))
  refine ⟨Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 K)), ?_⟩
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    F (𝓞 F) K (𝓞 K)]
  exact Nat.mul_comm _ _

/-- For a quadratic extension `K / F` of number fields, `|discr F| ^ 2 ≤ |discr K|`. -/
theorem quadratic_absolute_discriminant_square_le (hd : Module.finrank F K = 2) :
    (NumberField.discr F).natAbs ^ 2 ≤ (NumberField.discr K).natAbs := by
  simpa [hd] using absolute_discriminant_power_le K F

/-- Relative ramification index two forces the prime into the
finite discriminant cover. -/
theorem mem_discriminantPrimeIdealCover_of_ramification_two
    (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (he : Q.ramificationIdx (𝓞 F) = 2) :
    Q ∈ discriminantPrimeIdealCover K := by
  have : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
  obtain ⟨p, _, _, hpQ, hp, _⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q
  have hpz := Nat.prime_iff_prime_int.mp hp
  have hdiv : (p : ℤ) ∣ NumberField.discr K := by
    by_contra h
    have : Algebra.IsUnramifiedAt ℤ Q :=
      (NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) hpz).mp h
        Q inferInstance (by simp_all)
    have habs := Q.ramificationIdx_eq_one ℤ
    have hdvd :=
      Ideal.ramificationIdx_above_dvd (R := ℤ) (Q.under (𝓞 F)) Q
    simp_all
  apply Finset.mem_biUnion.mpr
  refine ⟨p, (by
    apply Nat.Prime.mem_primeFactors hp
    · simpa using Int.natAbs_dvd_natAbs.mpr hdiv
    · exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)), (Set.Finite.mem_toFinset _).mpr ⟨inferInstance, ?_⟩⟩
  apply (Ideal.liesOver_span_iff (inferInstance : Q.IsPrime).ne_top hpz).mpr
  simpa using hpQ

