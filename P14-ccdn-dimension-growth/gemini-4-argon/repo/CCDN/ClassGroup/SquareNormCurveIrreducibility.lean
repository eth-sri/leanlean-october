/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.ClassGroup.NormPolynomial
import CCDN.ClassGroup.NormPolynomialSubfield
import CCDN.Noether.ShearNormalization
import Mathlib.RingTheory.Polynomial.IsIntegral

/-! A double-cover polynomial with an odd root multiplicity is
irreducible. Applied to the norm-polynomial factorization, this detects
the even-index subfield exceptions. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial NumberField IntermediateField Module
open scoped IntermediateField

/-- Odd multiplicity of the generated subfield suffices, even when the
ambient number-field degree itself is even. -/
theorem signedNormCurvePolynomial_absolute_irreducible_of_odd_subfield_index
    (K : Type*) [Field K] [NumberField K]
    (β : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0)
    (hindex : Odd (Module.finrank ℚ⟮(β : K)⟯ K)) :
    AbsolutelyIrreducible (signedNormCurvePolynomial K β ε) := by
  apply (MulEquiv.irreducible_iff
    (f := bivariatePolynomialEquiv (AlgebraicClosure ℚ))).mp
  rw [← bivariatePolynomialEquiv_map]
  simp only [signedNormCurvePolynomial, AlgEquiv.apply_symm_apply]
  change Irreducible (Polynomial.map
    (Polynomial.mapRingHom (Int.castRingHom (AlgebraicClosure ℚ)))
    (X ^ 2 - C (C ε * integerNormPolynomial K β)))
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    coe_mapRingHom, Polynomial.map_mul]
  rw [integerNormPolynomial_map_eq_minpoly_pow_algebraicClosure]
  let F := AlgebraicClosure ℚ
  have hβ : IsIntegral ℚ (β : K) := IsIntegral.of_finite ℚ (β : K)
  let p := (minpoly ℚ (β : K)).map (algebraMap ℚ F)
  have hp : p.Separable := (minpoly.irreducible hβ).separable.map
  have hd : 0 < p.natDegree := by
    rw [(minpoly.monic hβ).natDegree_map]; exact minpoly.natDegree_pos hβ
  have hp0 : p ≠ 0 := fun h => by simp [h] at hd
  have hc : (ε : F) ≠ 0 := by exact_mod_cast hε
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p
    (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hd))
  have hrm_pow (r : F[X]) (hr : r ≠ 0) (n : ℕ) :
      rootMultiplicity a (r ^ n) = n * rootMultiplicity a r := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hr) hr), ih]; ring
  have hm : rootMultiplicity a p = 1 := by
    have := (rootMultiplicity_pos hp0).mpr ha
    have := rootMultiplicity_le_one_of_separable hp a
    omega
  let q := C (ε : F) * p ^ Module.finrank ℚ⟮(β : K)⟯ K
  have hq0 : q ≠ 0 := mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero _ hp0)
  have hodd : Odd (rootMultiplicity a q) := by
    rw [show rootMultiplicity a q = Module.finrank ℚ⟮(β : K)⟯ K by
      dsimp [q]
      rw [rootMultiplicity_mul hq0, rootMultiplicity_C, hrm_pow _ hp0, hm, mul_one, zero_add]]
    exact hindex
  apply (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc F) (monic_X_pow_sub_C q (by decide : (2 : ℕ) ≠ 0))).mpr
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  refine X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b he => ?_
  have hi := IsFractionRing.injective F[X] (RatFunc F)
  have hd_b : algebraMap F[X] (RatFunc F) b.denom ≠ 0 :=
    fun h => b.denom_ne_zero (hi (by simpa using h))
  have hb0 : b ≠ 0 := fun h =>
    hq0 (hi (by simpa using (by simpa [h] using he.symm : algebraMap F[X] (RatFunc F) q = 0)))
  have hnum : b.num ≠ 0 := RatFunc.num_ne_zero hb0
  have hpoly : b.num ^ 2 = q * b.denom ^ 2 := hi (by
    rw [map_pow, map_mul, map_pow, (div_eq_iff hd_b).mp b.num_div_denom, mul_pow, he])
  have hrm := congrArg (rootMultiplicity a) hpoly
  rw [hrm_pow _ hnum, rootMultiplicity_mul (mul_ne_zero hq0 (pow_ne_zero _ b.denom_ne_zero)),
    hrm_pow _ b.denom_ne_zero] at hrm
  obtain ⟨k, hk⟩ := hodd
  omega

end
end CCDN
