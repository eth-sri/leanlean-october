/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.AuxiliaryPolynomial.HypersurfaceBadReduction
public import CCDN.Plane.FiniteFieldConstants
import CCDN.AuxiliaryPolynomial.UniversalPlaneBadReduction

/-! The finite set of bad primes of an integer hypersurface. -/

public section
namespace CCDN
open MvPolynomial

/-- A polynomial with an irreducible image under a coefficient map is nonzero. -/
lemma ne_zero_of_irreducible_map {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    {φ : R →+* S} {f : MvPolynomial σ R} (h : Irreducible (map φ f)) : f ≠ 0 := by
  aesop

/-- Good reduction at a prime `p`: the reduction of `f` modulo `p` is nonzero and
absolutely irreducible. -/
noncomputable abbrev HasGoodReduction {σ : Type*} (f : MvPolynomial σ ℤ) (p : ℕ) [Fact p.Prime]  :=
  map (Int.castRingHom (ZMod p)) f ≠ 0 ∧
    Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f))

variable {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ] (f : MvPolynomial (Option σ) ℤ) (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f)) (hpos : 0 < f.totalDegree)

include hf hpos in
/-- Finiteness of the paper's bad-prime set above 27*d^4. A stronger set above
d is finite; filtering it gives the exact prescribed cutoff. -/
theorem finite_hypersurface_bad_primes
     :
    {p : ℕ | stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p}.Finite := by
  obtain ⟨rows, cols, e, he, hdiv⟩ := exists_integer_hypersurface_bad_prime_witness f hf hpos
  apply (((universalPlaneBadWitness f rows cols).coeff e).natAbs.primeFactors).finite_toSet.subset
  rintro p ⟨hp, hprime, hbad⟩
  let : Fact p.Prime := ⟨hprime⟩
  have hdegree : f.totalDegree < p := by
    have h2 := Nat.le_mul_self (f.totalDegree * f.totalDegree)
    have h3 : 27 * f.totalDegree ^ 4 < p := hp
    nlinarith
  refine Nat.mem_primeFactors.mpr ⟨hprime, ?_, Int.natAbs_ne_zero.mpr he⟩
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (hdiv p hdegree hbad)

end CCDN
