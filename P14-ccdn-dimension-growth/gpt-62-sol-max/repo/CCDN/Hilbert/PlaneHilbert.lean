/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredIntersection
import CCDN.ForMathlib.LinearMap
import CCDN.ForMathlib.MvPolynomial
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The exact affine Hilbert function of a principal plane equation. This
identifies polynomial total degree with the degree in the curve-counting target. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The polynomials in two variables of total degree at most `N` form a space of dimension `(N +
2).choose 2`. -/
theorem finrank_restrictTotalDegree_two {K : Type*} [Field K] (N : ℕ) :
    Module.finrank K (restrictTotalDegree (Fin 2) K N) = (N + 2).choose 2 := by
  rw [finrank_restrictTotalDegree]
  simp only [Fintype.card_fin]
  rw [Nat.add_comm 2 N, Nat.choose_symm_add]

/-- `2 · (n + 2).choose 2 = (n + 2)(n + 1)`. -/
lemma two_mul_choose_add_two (n : ℕ) :
    2 * (n + 2).choose 2 = (n + 2) * (n + 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (n + 2) 2
  norm_num [Nat.descFactorial_succ] at h
  nlinarith

/-- The affine Hilbert function of a nonzero plane equation `f` of degree `d` is `d N + d -
d(d-1)/2` for every `N ≥ d`. -/
theorem principal_plane_hilbert_function {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) {N : ℕ} (hN : f.totalDegree ≤ N) :
    (Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) N) : ℤ) =
      (f.totalDegree : ℤ) * N + ((f.totalDegree : ℤ) - f.totalDegree.choose 2) := by
  have h := principal_filtered_finrank f hf hN
  rw [finrank_restrictTotalDegree_two, finrank_restrictTotalDegree_two] at h
  have h0 := two_mul_choose_add_two N
  have h1 := two_mul_choose_add_two (N - f.totalDegree)
  have h2 := Nat.descFactorial_eq_factorial_mul_choose f.totalDegree 2
  norm_num [Nat.descFactorial_succ] at h2
  
  
  have hc1 : (2 : ℤ) * ((N - f.totalDegree + 2).choose 2 : ℤ) =
      ((N : ℤ) - f.totalDegree + 2) * ((N : ℤ) - f.totalDegree + 1) := by
    exact_mod_cast h1
  have hc2 : (2 : ℤ) * (f.totalDegree.choose 2 : ℤ) =
      (f.totalDegree : ℤ) * ((f.totalDegree : ℤ) - 1) := by
    grind
  nlinarith

/-- The principal plane ideal has filtered curve degree equal to the total degree. -/
lemma principal_plane_curve_degree {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) :
    HasFilteredCurveDegree (Ideal.span {f}) f.totalDegree :=
  ⟨_, _, fun _ hN => principal_plane_hilbert_function f hf hN⟩

end
end CCDN
