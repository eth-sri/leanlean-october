/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.PolynomialComparison
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! Linear growth is detected by comparing the Hilbert polynomial with an affine polynomial. -/

@[expose] public section
namespace CCDN
noncomputable section

open Polynomial in
/-- An eventual linear upper bound forces an eventual affine Hilbert function. -/
theorem filteredCoordinateSpace_eventually_linear
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) (D T : ℕ)
    (hbound : ∀ N ≥ T, Module.finrank K (filteredCoordinateSpace I N) ≤ D * (N + 2)) :
    ∃ d, HasFilteredCurveDegree I d := by
  let P := filteredHilbertPolynomial I
  let Q := C (D : ℚ) * X + C (2 * (D : ℚ))
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec I
  have hdeg : P.natDegree ≤ Q.natDegree := by
    apply polynomial_natDegree_le_of_eventual_nat_eval_le P Q
      (filteredHilbertPolynomial_leadingCoeff_pos I hI)
    refine ⟨max N T, fun n hn => ?_⟩
    rw [show P.eval (n : ℚ) = _ from hN n (le_of_max_le_left hn)]
    simp only [Q, eval_add, eval_mul, eval_C, eval_X]
    exact_mod_cast (show Module.finrank K (filteredCoordinateSpace I n) ≤ D * n + 2 * D from
      (hbound n (le_of_max_le_right hn)).trans_eq (by ring))
  have hP : P.natDegree ≤ 1 := hdeg.trans (by
    rw [show Q = _ from rfl, natDegree_add_C]
    simpa only [pow_one] using (natDegree_C_mul_X_pow_le (D : ℚ) 1))
  have hcoeff : ∃ d : ℕ, P.coeff 1 = (d : ℚ) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hP with hp | hp
    · exact ⟨0, by simpa using (coeff_eq_zero_of_natDegree_lt (show P.natDegree < 1 by omega))⟩
    obtain ⟨d, _, _, hd⟩ := filteredHilbertPolynomial_positive_multiplicity I hI
    exact ⟨d, by rw [← hp, coeff_natDegree, hd, hp]; simp⟩
  obtain ⟨d, hd⟩ := hcoeff
  have hline (n : ℕ) (hn : N ≤ n) :
      (Module.finrank K (filteredCoordinateSpace I n) : ℚ) = (d : ℚ) * n + P.coeff 0 := by
    rw [← hN n hn]
    change P.eval _ = _
    nth_rw 1 [eq_X_add_C_of_natDegree_le_one hP]
    simp [hd]
  refine ⟨d, N, (Module.finrank K (filteredCoordinateSpace I N) : ℤ) - (d : ℤ) * N, fun n hn => ?_⟩
  have he := hline n hn
  have he' := hline N le_rfl
  exact_mod_cast (show (Module.finrank K (filteredCoordinateSpace I n) : ℚ) =
    (d : ℚ) * n + ((Module.finrank K (filteredCoordinateSpace I N) : ℚ) - (d : ℚ) * N) by linarith)

open Polynomial in
/-- An eventual Hilbert slope is the linear coefficient of the Hilbert polynomial. -/
theorem HasFilteredCurveDegree.polynomial_eq {K σ : Type*} [Field K] [Fintype σ]
    [LinearOrder σ] {I : Ideal (MvPolynomial σ K)} {d : ℕ} (h : HasFilteredCurveDegree I d) :
    ∃ c : ℤ, filteredHilbertPolynomial I = C (d : ℚ) * X + C (c : ℚ) := by
  obtain ⟨N, c, hc⟩ := h
  refine ⟨c, filteredHilbertPolynomial_eq_of_eventual I _ ⟨N, fun n hn => ?_⟩⟩
  simp only [eval_add, eval_mul, eval_C, eval_X]
  exact_mod_cast (hc n hn).symm

/-- Positive Hilbert slope means Hilbert dimension one. -/
theorem HasFilteredCurveDegree.natDegree_eq_one {K σ : Type*} [Field K] [Fintype σ]
    [LinearOrder σ] {I : Ideal (MvPolynomial σ K)} {d : ℕ} (h : HasFilteredCurveDegree I d)
    (hd : 0 < d) : (filteredHilbertPolynomial I).natDegree = 1 := by
  obtain ⟨c, hc⟩ := h.polynomial_eq
  rw [hc, Polynomial.natDegree_linear (by positivity)]

/-- A positive eventual slope gives affine dimension one and the same multiplicity. -/
theorem HasFilteredCurveDegree.dimension_degree {K σ : Type*} [Field K] [Fintype σ]
    [LinearOrder σ] {I : Ideal (MvPolynomial σ K)} {d : ℕ} (h : HasFilteredCurveDegree I d)
    (hd : 0 < d) : HasAffineDimensionDegree I 1 d := by
  obtain ⟨c, hc⟩ := h.polynomial_eq
  refine ⟨h.natDegree_eq_one hd, ?_⟩
  rw [hc, Polynomial.leadingCoeff_linear (by positivity)]
  simp

/-- The powers `1, u, …, u ^ (N - 1)` of a transcendental element `u` are linearly independent. -/
private lemma transcendental_powers_independent {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (u : R) (hu : Transcendental K u) (N : ℕ) :
    LinearIndependent K (fun i : Fin N => u ^ i.val) := by
  have hb := (Polynomial.basisMonomials K).linearIndependent.map'
    (Polynomial.aeval u).toLinearMap
    (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hu))
  have hh := hb.comp (fun i : Fin N => i.val) Fin.val_injective
  simpa only [Function.comp_def, Polynomial.coe_basisMonomials, AlgHom.toLinearMap_apply,
    Polynomial.aeval_monomial, map_one, one_mul] using hh

section
variable {K σ : Type*} [Field K] [Fintype σ]
include K σ

/-- A transcendental coordinate contributes all of its powers to the filtration. -/
theorem transcendental_coordinate_filtered_lower
    (I : Ideal (MvPolynomial σ K)) {j : σ}
    (hj : Transcendental K ((Ideal.Quotient.mk I) (MvPolynomial.X j))) (N : ℕ) :
    N + 1 ≤ Module.finrank K (filteredCoordinateSpace I N) := by
  classical
  have hlin := transcendental_powers_independent
    ((Ideal.Quotient.mk I) (MvPolynomial.X j)) hj (N + 1)
  have hmem (k : Fin (N + 1)) :
      ((Ideal.Quotient.mk I) (MvPolynomial.X j)) ^ k.val ∈ filteredCoordinateSpace I N := by
    refine mem_filteredCoordinateSpace.mpr ⟨MvPolynomial.X j ^ k.val, ?_, by simp⟩
    rw [MvPolynomial.totalDegree_X_pow]
    omega
  let v : Fin (N + 1) → filteredCoordinateSpace I N :=
    fun k => ⟨((Ideal.Quotient.mk I) (MvPolynomial.X j)) ^ k.val, hmem k⟩
  have hv : LinearIndependent K v :=
    LinearIndependent.of_comp (filteredCoordinateSpace I N).subtype hlin
  simpa using hv.fintype_card_le_finrank

end

end
end CCDN
