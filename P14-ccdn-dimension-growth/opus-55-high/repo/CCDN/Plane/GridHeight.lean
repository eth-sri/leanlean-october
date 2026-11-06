/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.BivariateTotalDegree
import Mathlib.Basic.Real.Basic
import CCDN.Height.MultivariateGridHeight
import CCDN.Noether.ShearNormalization

/-! A coefficient-height witness on the bounded integer plane grid: the case n = 2 of
`CCDN.Height.MultivariateGridHeight`. -/

namespace CCDN
section
open Polynomial

section
variable {R : Type*} [CommRing R]

/-- Evaluating the nested-polynomial form of a bivariate polynomial `f` at `(x, y)` (inner
variable at `y`, outer variable at `x`) agrees with evaluating `f` at `![x, y]`. -/
lemma bivariatePolynomialEquiv_eval
    (f : MvPolynomial (Fin 2) R) (x y : R) :
    (Polynomial.map (Polynomial.evalRingHom y) (bivariatePolynomialEquiv R f)).eval x =
      MvPolynomial.eval ![x, y] f := by
  have he : (Polynomial.evalRingHom x).comp
      ((Polynomial.mapRingHom (Polynomial.evalRingHom y)).comp
        (bivariatePolynomialEquiv R).toRingHom) =
      MvPolynomial.eval ![x, y] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [bivariatePolynomialEquiv_C]
    · intro i
      fin_cases i <;> simp [bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
  exact RingHom.congr_fun he f

/-- Natural-number points of `Fin 2 → ℕ`, written as vectors of length two. -/
lemma natCast_fin_two_eq (a : Fin 2 → ℕ) :
    (fun i => (a i : R)) = ![(a 0 : R), (a 1 : R)] := by
  funext i
  fin_cases i <;> rfl

end

/-- The plane case of `multivariate_coefficient_bound_of_integer_grid`, for nested
polynomials. -/
theorem bivariate_coefficient_bound_of_integer_grid (f : ℝ[X][X]) {d : ℕ}
    (hd : bivariateTotalDegree f ≤ d) {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ x y : ℕ, x ≤ d → y ≤ d →
      |(Polynomial.map (Polynomial.evalRingHom (y : ℝ)) f).eval (x : ℝ)| ≤ H) (i j : ℕ) :
    |(f.coeff i).coeff j| ≤ ((d : ℝ) + 1) ^ (2 * (d + 1)) * H := by
  have h := multivariate_coefficient_bound_of_integer_grid
    ((bivariatePolynomialEquiv ℝ).symm f) hd hH (fun a ha => by
      have hh := heval (a 0) (a 1) (ha 0) (ha 1)
      rwa [← (bivariatePolynomialEquiv ℝ).apply_symm_apply f, bivariatePolynomialEquiv_eval,
        ← natCast_fin_two_eq] at hh) (Finsupp.cons i (Finsupp.single 0 j))
  rwa [← bivariatePolynomialEquiv_coeff, AlgEquiv.apply_symm_apply] at h


