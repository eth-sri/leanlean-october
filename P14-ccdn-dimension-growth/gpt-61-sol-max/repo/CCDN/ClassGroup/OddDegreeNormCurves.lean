/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.ClassGroup.NormPolynomial
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.Polynomial.IsIntegral

/-! The full odd-degree norm polynomial gives an absolutely irreducible
double-cover equation. No squarefree-part substitution is made. -/

public section
namespace CCDN
open scoped NumberField
open Polynomial NumberField

variable {F : Type*} [Field F] (p : F[X]) (hp : Odd p.natDegree)

include hp in
private lemma odd_degree_polynomial_not_square_ratFunc  (b : RatFunc F) :
    b ^ 2 ≠ algebraMap F[X] (RatFunc F) p := by
  intro he
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  have hb : b ≠ 0 := by
    intro h
    have hz : algebraMap F[X] (RatFunc F) p = 0 := by simpa [h] using he.symm
    exact hp0 ((IsFractionRing.injective F[X] (RatFunc F)) (by simpa using hz))
  have hd := congrArg RatFunc.intDegree he
  rw [sq, RatFunc.intDegree_mul hb hb, RatFunc.intDegree_polynomial] at hd
  obtain ⟨k, hk⟩ := hp
  omega

include hp in
/-- For a polynomial `p` of odd degree over a field `F`, the double-cover polynomial `Y ^ 2 - p` is
irreducible in `F[X][Y]`. -/
lemma odd_degree_double_cover_irreducible  :
    Irreducible (X ^ 2 - C p : F[X][X]) := by
  apply (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc F) (monic_X_pow_sub_C p (by decide : 2 ≠ 0))).mpr
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_two
    (odd_degree_polynomial_not_square_ratFunc p hp)

/-- For a polynomial `p` of degree at least `2`, the double-cover polynomial `Y ^ 2 - p` has total
degree `deg p`. -/
lemma double_cover_bivariateTotalDegree {R : Type*} [CommRing R] [Nontrivial R]
    (p : R[X]) (hp : 2 ≤ p.natDegree) :
    bivariateTotalDegree (X ^ 2 - C p : R[X][X]) = p.natDegree := by
  apply le_antisymm
  · rw [bivariateTotalDegree_le_iff]
    intro i j hij
    by_cases hi : i = 2
    · aesop
    · by_cases hi0 : i = 0
      · simp_all [le_natDegree_of_ne_zero]
      · aesop
  · have hp0 : p ≠ 0 := by intro h; simp [h] at hp
    have h := bivariateTotalDegree_coeff_le (X ^ 2 - C p : R[X][X]) 0 p.natDegree
      (by simp_all)
    simpa using h

/-- For `[K : ℚ] ≥ 2` and `ε ≠ 0`, the signed norm-curve polynomial `y ^ 2 - ε * N(x - β)` has total
degree `[K : ℚ]`. -/
theorem signedNormCurvePolynomial_totalDegree (K : Type*) [Field K] [NumberField K]
    (β : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0) (hn : 2 ≤ Module.finrank ℚ K) :
    (signedNormCurvePolynomial K β ε).totalDegree = Module.finrank ℚ K := by
  have hd : (C ε * integerNormPolynomial K β).natDegree = Module.finrank ℚ K := by
    rw [natDegree_C_mul hε, integerNormPolynomial_natDegree]
  change bivariateTotalDegree (X ^ 2 - C (C ε * integerNormPolynomial K β)) = _
  rw [double_cover_bivariateTotalDegree _ (by omega), hd]

end CCDN
