/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.ClassGroup.NormPolynomial
import CCDN.ClassGroup.NormPolynomialSubfield
import CCDN.ClassGroup.OddDegreeNormCurves
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

private lemma rootMultiplicity_pow_exact {F : Type*} [Field F] (a : F) (p : F[X]) (n : ℕ) :
    rootMultiplicity a (p ^ n) = n * rootMultiplicity a p := by
  classical
  rw [← count_roots, roots_pow, Multiset.count_nsmul, count_roots]

private lemma double_cover_irreducible_of_odd_root_multiplicity {F : Type*} [Field F]
    (p : F[X]) (a : F) (ha : Odd (rootMultiplicity a p)) :
    Irreducible (X ^ 2 - C p : F[X][X]) := by
  apply double_cover_irreducible_of_nonsquare
  intro q h
  rw [← h, rootMultiplicity_pow_exact] at ha
  grind

private lemma separable_odd_power_double_cover_irreducible
    {F : Type*} [Field F] [IsAlgClosed F]
    (p : F[X]) (hp : p.Separable) (hd : 0 < p.natDegree)
    {c : F} (hc : c ≠ 0) {e : ℕ} (he : Odd e) :
    Irreducible (X ^ 2 - C (C c * p ^ e) : F[X][X]) := by
  have hp0 : p ≠ 0 := by aesop
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    exact ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hd))
  have hm : rootMultiplicity a p = 1 := by
    have hpos := (rootMultiplicity_pos hp0).mpr ha
    have hle := rootMultiplicity_le_one_of_separable hp a
    omega
  apply double_cover_irreducible_of_odd_root_multiplicity (C c * p ^ e) a
  rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero _ hp0)),
    rootMultiplicity_C, rootMultiplicity_pow_exact, hm, mul_one, zero_add]
  exact he

/-- Odd multiplicity of the generated subfield suffices, even when the
ambient number-field degree itself is even. -/
theorem signedNormCurvePolynomial_absolute_irreducible_of_odd_subfield_index
    (K : Type*) [Field K] [NumberField K]
    (β : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0)
    (hindex : Odd (Module.finrank ℚ⟮(β : K)⟯ K)) :
    AbsolutelyIrreducible (signedNormCurvePolynomial K β ε) := by
  apply (MulEquiv.irreducible_iff
    (f := bivariatePolynomialEquiv (AlgebraicClosure ℚ))).mp
  rw [signedNormCurvePolynomial_bivariate_map,
    integerNormPolynomial_map_eq_minpoly_pow_algebraicClosure]
  have hβ := IsIntegral.of_finite ℚ (β : K)
  apply separable_odd_power_double_cover_irreducible
    ((minpoly ℚ (β : K)).map (algebraMap ℚ (AlgebraicClosure ℚ)))
    ((minpoly.irreducible hβ).separable.map) _ _ hindex
  · rw [(minpoly.monic hβ).natDegree_map]
    exact minpoly.natDegree_pos hβ
  simp_all

end
end CCDN
