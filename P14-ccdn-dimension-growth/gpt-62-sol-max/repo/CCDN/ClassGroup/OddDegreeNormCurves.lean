/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.NormPolynomial
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.IsIntegral

/-! The full odd-degree norm polynomial gives an absolutely irreducible
double-cover equation. No squarefree-part substitution is made. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField
open Polynomial NumberField

/-- A polynomial nonsquare stays nonsquare in the rational function field by integral closure. -/
lemma double_cover_irreducible_of_nonsquare {F : Type*} [Field F]
    (p : F[X]) (hp : ∀ q : F[X], q ^ 2 ≠ p) :
    Irreducible (X ^ 2 - C p : F[X][X]) := by
  apply (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc F) (monic_X_pow_sub_C p (by decide : (2 : ℕ) ≠ 0))).mpr
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro b hb
  obtain ⟨q, rfl⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by decide) (hb ▸ isIntegral_algebraMap)
  exact hp q (IsFractionRing.injective F[X] (RatFunc F) (by simp_all))

/-- An odd-degree polynomial cannot be a square. -/
lemma odd_degree_double_cover_irreducible {F : Type*} [Field F] (p : F[X]) (hp : Odd p.natDegree) :
    Irreducible (X ^ 2 - C p : F[X][X]) := by
  apply double_cover_irreducible_of_nonsquare
  intro q h
  have hdeg := congrArg natDegree h
  rw [natDegree_pow] at hdeg
  grind

/-- For a polynomial `p` of degree at least `2`, the double-cover polynomial `Y ^ 2 - p` has total
degree `deg p`. -/
lemma double_cover_bivariateTotalDegree {R : Type*} [CommRing R] [Nontrivial R]
    (p : R[X]) (hp : 2 ≤ p.natDegree) :
    bivariateTotalDegree (X ^ 2 - C p : R[X][X]) = p.natDegree := by
  apply le_antisymm
  · rw [bivariateTotalDegree_le_iff]
    intro i j hij
    by_cases hi : i = 2
    aesop
    · by_cases hi0 : i = 0
      simp_all [le_natDegree_of_ne_zero]
      aesop
  · have hp0 : p ≠ 0 := by aesop
    have h := bivariateTotalDegree_coeff_le (X ^ 2 - C p : R[X][X]) 0 p.natDegree
      (by simp_all)
    simpa using h


end
end CCDN
