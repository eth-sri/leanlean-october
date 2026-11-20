module

public import ValuedFieldTheory.Valuation.Henselian.Factorization.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# coefficientwise limit preparation

This file records the coefficientwise Cauchy form of the infinite Hensel
approximants.  It is the input needed for the adic-completeness step in
the coefficientwise proof of Hensel's lemma.
-/

noncomputable section

open scoped Polynomial
open scoped BigOperators

namespace AlgebraicNumberTheory
namespace Valuations

/-- the directed adic Cauchy estimate for a coefficient
sequence: later differences from stage `M` lie in `I^(M+1)`. -/
def henselFactorization_adicCoeffCauchy
    {R : Type*} [CommRing R] (I : Ideal R) (x : ℕ → R) : Prop :=
  ∀ {M N : ℕ}, M ≤ N → x N - x M ∈ I ^ (M + 1)

section

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- A coefficientwise Cauchy estimate for a polynomial sequence gives an
adic Cauchy estimate for each fixed coefficient. -/
theorem henselFactorization_coeff_adicCoeffCauchy_of_sub_coeff_mem {Pseq : ℕ → R[X]}
    (hsub :
      ∀ {M N : ℕ}, M ≤ N → ∀ i : ℕ,
        (Pseq N - Pseq M).coeff i ∈ I ^ (M + 1))
    (i : ℕ) :
    henselFactorization_adicCoeffCauchy I (fun N : ℕ => (Pseq N).coeff i) := by
  simp_all [henselFactorization_adicCoeffCauchy]

/-- the coefficientwise `I^(M+1)` estimate gives mathlib's
`I`-adic Cauchy condition after weakening `I^(M+1) ≤ I^M`. -/
theorem henselFactorization_adicCoeffCauchy_isAdicCauchy {x : ℕ → R}
    (hx : henselFactorization_adicCoeffCauchy I x) :
    AdicCompletion.IsAdicCauchy I R x := by
  intro M N hMN
  apply SModEq.sub_mem.mpr
  exact (by
    simpa [neg_sub] using (I ^ M).neg_mem (Ideal.pow_le_pow_right (Nat.le_succ M) (hx hMN)))

/-- precompleteness supplies a coefficient limit for every
coefficient sequence satisfying the directed estimate. -/
theorem henselFactorization_exists_adicCoeffLimit [IsPrecomplete I R]
    {x : ℕ → R}
    (hx : henselFactorization_adicCoeffCauchy I x) :
    ∃ L : R, ∀ n : ℕ, x n - L ∈ I ^ n := by
  obtain ⟨L, hL⟩ :=
    IsPrecomplete.prec (show IsPrecomplete I R from inferInstance)
      (henselFactorization_adicCoeffCauchy_isAdicCauchy I hx)
  refine ⟨L, fun n => ?_⟩
  simpa using (SModEq.sub_mem.mp (hL n))

end

/-- assemble finitely many coefficient limits into the
polynomial supported in degrees at most `N`. -/
def henselFactorization_polyOfLimitCoeffs
    {R : Type*} [Semiring R] (N : ℕ) (c : ℕ → R) : R[X] :=
  Finset.sum (Finset.range (N + 1)) fun i => Polynomial.monomial i (c i)

section

variable {R : Type*} [Semiring R] {N n : ℕ} (c : ℕ → R)

/-- coefficients of the finite polynomial assembled from
coefficient limits, inside the cutoff. -/
theorem henselFactorization_polyOfLimitCoeffs_coeff_of_le (hn : n ≤ N) :
    (henselFactorization_polyOfLimitCoeffs N c).coeff n = c n := by
  classical
  unfold henselFactorization_polyOfLimitCoeffs
  simp
  rw [Finset.sum_eq_single n]
  · simp
  · simp_all [Polynomial.coeff_monomial]
  · grind [False.elim]

/-- coefficients of the finite polynomial assembled from
coefficient limits vanish above the cutoff. -/
theorem henselFactorization_polyOfLimitCoeffs_coeff_eq_zero_of_lt (hn : N < n) :
    (henselFactorization_polyOfLimitCoeffs N c).coeff n = 0 := by
  classical
  simp_all [henselFactorization_polyOfLimitCoeffs, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

end

/-- the polynomial assembled from finitely many coefficient
limits has the stated degree bound. -/
theorem henselFactorization_polyOfLimitCoeffs_natDegree_le
    {R : Type*} [Semiring R] (N : ℕ) (c : ℕ → R) :
    (henselFactorization_polyOfLimitCoeffs N c).natDegree ≤ N := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  grind [henselFactorization_polyOfLimitCoeffs_coeff_eq_zero_of_lt]

/-- bounded polynomial approximants with coefficientwise
adic limits have a bounded polynomial limit. -/
theorem henselFactorization_exists_limitPolynomial_of_bounded_coeffLimits
    {R : Type*} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    {N : ℕ} {Pseq : ℕ → R[X]}
    (hdeg : ∀ n : ℕ, (Pseq n).natDegree ≤ N)
    (hcauchy :
      ∀ i : ℕ, henselFactorization_adicCoeffCauchy I
        (fun n : ℕ => (Pseq n).coeff i)) :
    ∃ P : R[X], P.natDegree ≤ N ∧
      ∀ n i : ℕ, (Pseq n - P).coeff i ∈ I ^ n := by
  classical
  let L : ℕ → R :=
    fun i =>
      Classical.choose
        (henselFactorization_exists_adicCoeffLimit (I := I) (hcauchy i))
  let P := henselFactorization_polyOfLimitCoeffs N L
  refine ⟨P, henselFactorization_polyOfLimitCoeffs_natDegree_le N L, ?_⟩
  intro n i
  by_cases hi : i ≤ N
  · simpa [P, L, Polynomial.coeff_sub, henselFactorization_polyOfLimitCoeffs_coeff_of_le, hi] using Classical.choose_spec (henselFactorization_exists_adicCoeffLimit (I := I) (hcauchy i)) n
  · have hlt : N < i := Nat.lt_of_not_ge hi
    have hP : P.coeff i = 0 :=
      henselFactorization_polyOfLimitCoeffs_coeff_eq_zero_of_lt (c := L) hlt
    simp [Polynomial.coeff_sub, (Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (hdeg n) hlt)), hP]

/-- if all coefficients of the left factor lie in an ideal,
then all coefficients of its product with any polynomial lie in the same
ideal. -/
theorem henselFactorization_mul_left_coeff_mem_ideal
    {R : Type*} [CommRing R] (I : Ideal R) {A B : R[X]}
    (hA : ∀ i : ℕ, A.coeff i ∈ I) :
    ∀ i : ℕ, (A * B).coeff i ∈ I := by
  intro i
  rw [Polynomial.coeff_mul]
  exact I.sum_mem fun p _hp => I.mul_mem_right _ (hA p.1)

/-- if all coefficients of the right factor lie in an ideal,
then all coefficients of its product with any polynomial lie in the same
ideal. -/
theorem henselFactorization_mul_right_coeff_mem_ideal
    {R : Type*} [CommRing R] (I : Ideal R) {A B : R[X]}
    (hB : ∀ i : ℕ, B.coeff i ∈ I) :
    ∀ i : ℕ, (A * B).coeff i ∈ I := by
  intro i
  rw [Polynomial.coeff_mul]
  exact I.sum_mem fun p _hp => I.mul_mem_left _ (hB p.2)

section

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- coefficientwise convergence is preserved by multiplying
two polynomial approximants. -/
theorem henselFactorization_mul_sub_mul_coeff_mem_of_coeff_mem {A A' B B' : R[X]}
    (hA : ∀ i : ℕ, (A - A').coeff i ∈ I)
    (hB : ∀ i : ℕ, (B - B').coeff i ∈ I) :
    ∀ i : ℕ, (A * B - A' * B').coeff i ∈ I := by
  have hdecomp : A * B - A' * B' = (A - A') * B + A' * (B - B') := by
    ring
  intro i
  simp [hdecomp]
  exact Ideal.add_mem I (henselFactorization_mul_left_coeff_mem_ideal I hA i) (henselFactorization_mul_right_coeff_mem_ideal I hB i)

/-- combine the product convergence with the residual error
estimate at one adic level. -/
theorem henselFactorization_limit_factor_coeff_mem_of_approximants
    {f G H Gn Hn : R[X]}
    (herr : ∀ i : ℕ, (f - Gn * Hn).coeff i ∈ I)
    (hG : ∀ i : ℕ, (Gn - G).coeff i ∈ I)
    (hH : ∀ i : ℕ, (Hn - H).coeff i ∈ I) :
    ∀ i : ℕ, (f - G * H).coeff i ∈ I := by
  have hdecomp : f - G * H = (f - Gn * Hn) + (Gn * Hn - G * H) := by
    ring
  intro i
  rw [hdecomp, Polynomial.coeff_add]
  exact I.add_mem (herr i)
    (henselFactorization_mul_sub_mul_coeff_mem_of_coeff_mem
      (I := I) hG hH i)

end

/-- a polynomial whose coefficients lie in every adic power is
zero in a Hausdorff coefficient ring. -/
theorem henselFactorization_polynomial_eq_zero_of_coeff_mem_all_powers
    {R : Type*} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    {P : R[X]}
    (hP : ∀ n i : ℕ, P.coeff i ∈ I ^ n) :
    P = 0 := by
  ext i
  apply IsHausdorff.haus (show IsHausdorff I R from inferInstance)
  intro n
  simp_all [SModEq.sub_mem]

section

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- if the approximating factorization and both factors
converge coefficientwise at every adic level, then the limiting polynomials
factor `f`. -/
theorem henselFactorization_limit_factor_eq_of_approximants [IsHausdorff I R]
    {f G H : R[X]} {Gseq Hseq : ℕ → R[X]}
    (herr : ∀ n i : ℕ, (f - Gseq n * Hseq n).coeff i ∈ I ^ n)
    (hG : ∀ n i : ℕ, (Gseq n - G).coeff i ∈ I ^ n)
    (hH : ∀ n i : ℕ, (Hseq n - H).coeff i ∈ I ^ n) :
    f = G * H := by
  exact sub_eq_zero.mp (henselFactorization_polynomial_eq_zero_of_coeff_mem_all_powers I fun n i ↦ henselFactorization_limit_factor_coeff_mem_of_approximants (I ^ n) (herr n) (hG n) (hH n) i)

/-- the limit of approximants preserving a fixed residual
class preserves that residual class.  Only the first adic level is needed. -/
theorem henselFactorization_limit_reduction_of_approx_reduction
    {P P0 : R[X]} {Pseq : ℕ → R[X]}
    (hlim : ∀ n i : ℕ, (Pseq n - P).coeff i ∈ I ^ n)
    (hred : ∀ n i : ℕ, (Pseq n - P0).coeff i ∈ I) :
    ∀ i : ℕ, (P - P0).coeff i ∈ I := by
  intro i
  have hlim1 : (Pseq 1 - P).coeff i ∈ I := by
    simpa using hlim 1 i
  have hred1 := hred 1 i
  have hdecomp : P - P0 = -(Pseq 1 - P) + (Pseq 1 - P0) := by
    ring
  rw [hdecomp, Polynomial.coeff_add, Polynomial.coeff_neg]
  exact I.add_mem (I.neg_mem hlim1) hred1

end

/-- coefficientwise membership in a ring-hom kernel gives
equality after mapping coefficients. -/
theorem henselFactorization_map_eq_of_sub_coeff_mem_ker
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    {P Q : R[X]}
    (hcoeff : ∀ i : ℕ, (P - Q).coeff i ∈ RingHom.ker φ) :
    P.map φ = Q.map φ := by
  have hzero :=
    (henselFactorization_map_eq_zero_iff_coeff_mem_ker φ (P - Q)).2 hcoeff
  simp at hzero
  exact sub_eq_zero.mp hzero

/-- coefficientwise maximal-ideal congruence is exactly
equality after mapping to the residue field. -/
theorem henselFactorization_residue_map_eq_of_sub_coeff_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] {P Q : R[X]}
    (hcoeff : ∀ i : ℕ, (P - Q).coeff i ∈ IsLocalRing.maximalIdeal R) :
    P.map (IsLocalRing.residue R) = Q.map (IsLocalRing.residue R) := by
  apply henselFactorization_map_eq_of_sub_coeff_mem_ker
  intro i
  simp_all [IsLocalRing.ker_residue]

end Valuations
end AlgebraicNumberTheory

end
