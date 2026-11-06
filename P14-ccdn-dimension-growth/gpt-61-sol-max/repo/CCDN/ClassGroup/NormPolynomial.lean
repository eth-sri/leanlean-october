/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Noether.BivariateTotalDegree
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import CCDN.Plane.GridHeight

/-! Integral norm polynomials and the two signed plane equations
needed to count square-norm generators. The norm polynomial retains the full
number-field degree even when its parameter lies in a proper subfield. -/

@[expose] public section
namespace CCDN
open scoped NumberField
open NumberField Polynomial

variable (K : Type*) [Field K] [NumberField K]

variable (β : 𝓞 K)

/-- The integer norm polynomial of `β ∈ 𝓞 K`: the characteristic polynomial of multiplication by
`β`, whose value at `x ∈ ℤ` is the norm `N(x - β)`. -/
noncomputable def integerNormPolynomial   :=
  (Algebra.lmul ℤ (𝓞 K) β).charpoly

/-- The integer norm polynomial of an algebraic integer is monic. -/
lemma integerNormPolynomial_monic  :
    (integerNormPolynomial K β).Monic :=
  LinearMap.charpoly_monic _

/-- The integer norm polynomial of an algebraic integer of `K` has degree `[K : ℚ]`. -/
lemma integerNormPolynomial_natDegree  :
    (integerNormPolynomial K β).natDegree = Module.finrank ℚ K := by
  rw [integerNormPolynomial, LinearMap.charpoly_natDegree, RingOfIntegers.rank]

/-- The integer norm polynomial of `β` evaluated at `x ∈ ℤ` is the norm `N(x - β)`. -/
lemma integerNormPolynomial_eval  (x : ℤ) :
    (integerNormPolynomial K β).eval x =
      Algebra.norm ℤ (algebraMap ℤ (𝓞 K) x - β) := by
  rw [integerNormPolynomial, LinearMap.eval_charpoly, Algebra.norm_apply,
    map_sub (Algebra.lmul ℤ (𝓞 K)), Algebra.lmul_algebraMap]
  rfl

/-- The signed norm-curve polynomial `y ^ 2 - ε * N(x - β)` in the plane coordinates `(y, x)`,
where `N(x - β)` is the integer norm polynomial of `β`: on an integral point the first
coordinate is a square root of the norm and the second is the integral translation parameter. -/
noncomputable def signedNormCurvePolynomial  (ε : ℤ)  :=
  (bivariatePolynomialEquiv ℤ).symm
    (X ^ 2 - C (C ε * integerNormPolynomial K β))

private lemma signedNormCurvePolynomial_eval  (ε x y : ℤ) :
    MvPolynomial.eval ![y, x] (signedNormCurvePolynomial K β ε) =
      y ^ 2 - ε * Algebra.norm ℤ (algebraMap ℤ (𝓞 K) x - β) := by
  rw [← bivariatePolynomialEquiv_eval _ y x]
  simp [signedNormCurvePolynomial, integerNormPolynomial_eval]

/-- If `|N(x - β)| = m ^ 2`, then `(m, x)` is an integral point on one of the two signed norm curves
`y ^ 2 = N(x - β)` or `y ^ 2 = -N(x - β)`. -/
lemma square_norm_yields_signedNormCurve_point
     (x : ℤ) (m : ℕ)
    (h : (Algebra.norm ℤ (algebraMap ℤ (𝓞 K) x - β)).natAbs = m ^ 2) :
    MvPolynomial.eval ![↑m, x] (signedNormCurvePolynomial K β 1) = 0 ∨
      MvPolynomial.eval ![↑m, x] (signedNormCurvePolynomial K β (-1)) = 0 := by
  grind [signedNormCurvePolynomial_eval]

end CCDN
