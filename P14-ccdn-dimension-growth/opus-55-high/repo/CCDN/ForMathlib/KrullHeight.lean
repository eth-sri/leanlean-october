/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.IntegralClosure.GoingDown

/-!
# Krull heights of contracted primes and of two-equation intersections

## Main results

* `Ideal.height_under_eq_one_of_height_le_one`: a nonzero prime of height at most one in an
  integral extension of a normal Noetherian domain contracts to a prime of height one.
* `Ideal.isPrincipal_under_of_height_le_one`: over a unique factorization domain, that
  contraction is principal.
* `Ideal.height_eq_two_of_mem_minimalPrimes_span_pair`: if `f` is prime and does not divide
  `g`, every minimal prime of `(f, g)` has height two.
-/

namespace Ideal

/-- A nontrivial two-equation intersection with prime first equation is purely
of codimension two: all its minimal primes have height two. -/
theorem height_eq_two_of_mem_minimalPrimes_span_pair {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {f g : R} (hf : Prime f) (hfg : ¬ f ∣ g)
    {p : Ideal R} (hp : p ∈ (Ideal.span ({f, g} : Set R)).minimalPrimes) :
    p.height = 2 := by
  classical
  have : p.IsPrime := hp.isPrime
  let : (Ideal.span ({f} : Set R)).IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr hf
  have hpf : Ideal.span ({f} : Set R) ≤ p :=
    (Ideal.span_mono (by grind)).trans hp.le
  have h1 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf.ne_zero) hf.not_isUnit
  have hlo := Ideal.height_add_one_le_of_lt_of_isPrime (by
    apply lt_of_le_of_ne hpf
    intro he
    exact hfg (Ideal.mem_span_singleton.mp (he ▸ (hp.le (Ideal.subset_span (by simp))))))
  rw [h1] at hlo
  have hhi : p.height ≤ 2 := by
    have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
      (s := ({f, g} : Finset R)) (by aesop)
    exact h.trans (mod_cast (Finset.card_le_two : ({f, g} : Finset R).card ≤ 2))
  norm_num at hlo
  exact hhi.antisymm hlo

