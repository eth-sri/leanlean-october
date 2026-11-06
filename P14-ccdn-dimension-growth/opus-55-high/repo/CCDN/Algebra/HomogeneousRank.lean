/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousMonomials
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import CCDN.Algebra.HomogeneousEvaluation
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.FilteredIntersection
import CCDN.Hilbert.HomogeneousHilbert

/-! The homogeneous Hilbert count bounds evaluation-matrix ranks.
The deficit includes every degree-allowed multiple of the defining equation. -/

namespace CCDN
noncomputable section
open MvPolynomial Matrix

section
variable (K : Type*) [Field K] (n M : ℕ)

/-- The `K`-linear map sending a polynomial in `n + 1` variables to its vector of coefficients
at the degree-`M` monomials, enumerated by `homogeneousMonomials n M`. -/
def homogeneousCoefficientMap :
    MvPolynomial (Fin (n + 1)) K →ₗ[K] (Fin ((n + M).choose M) → K) :=
  LinearMap.pi fun j => lcoeff K (homogeneousMonomials n M j)

/-- The matrix of values of the degree-`M` monomials in `n + 1` variables at the points
`points i`: its `(i, j)` entry is the `j`-th monomial of `homogeneousMonomials n M` evaluated
at `points i`. -/
def homogeneousEvaluationMatrix {t : ℕ}
    (points : Fin t → (Fin (n + 1) → K)) : Matrix (Fin t) (Fin ((n + M).choose M)) K :=
  fun i j => (homogeneousMonomials n M j).prod fun k e => points i k ^ e

end

/-- For a homogeneous polynomial `f` of degree `M`, multiplying the homogeneous evaluation matrix
by the coefficient vector of `f` gives the vector of values of `f` at the points. -/
lemma homogeneous_evaluation_mulVec {K : Type*} [Field K] {n M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M)
    (points : Fin t → (Fin (n + 1) → K)) (i : Fin t) :
    (homogeneousEvaluationMatrix K n M points *ᵥ homogeneousCoefficientMap K n M f) i =
      eval (points i) f := by
  symm
  calc
    eval (points i) f = eval (points i)
        (∑ j, monomial (homogeneousMonomials n M j) (f.coeff (homogeneousMonomials n M j))) :=
        congrArg (eval (points i)) (homogeneous_eq_sum_coeff f hf)
    _ = _ := by
      simp [homogeneousEvaluationMatrix, homogeneousCoefficientMap, mulVec, dotProduct,
        eval_monomial, mul_comm]


/-- The homogeneous evaluation matrix of integer points, computed over `ℚ`, is the cast of the
integer evaluation matrix of the degree-`M` monomials. -/
lemma homogeneousEvaluationMatrix_intCast {n M t : ℕ}
    (points : Fin t → (Fin (n + 1) → ℤ)) :
    homogeneousEvaluationMatrix ℚ n M (fun i j => (points i j : ℚ)) =
      (evaluationMatrix (homogeneousMonomials n M) points).map ((↑) : ℤ → ℚ) := by
  ext i j
  simp [homogeneousEvaluationMatrix, evaluationMatrix]

