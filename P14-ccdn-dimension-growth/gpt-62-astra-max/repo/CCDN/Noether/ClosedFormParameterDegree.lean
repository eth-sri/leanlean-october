/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateCoefficientMatrix
import CCDN.Noether.ClosedFormEntry
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Parameter degrees of the closed-form matrix and its minors. Differentiation
in the two plane coordinates does not increase the parameter degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

section

variable {K τ : Type*} [CommRing K] {f : (MvPolynomial τ K)[X][X]} {D : ℕ}

/-- Every coefficient of the bivariate polynomial `f`, whose coefficients are polynomials in the
parameters `τ`, has total degree at most `D` in the parameters; the two polynomial variables are
the coordinates on the plane. -/
def BivariateParameterDegreeBound
    (f : (MvPolynomial τ K)[X][X]) (D : ℕ) : Prop :=
  ∀ i j, ((f.coeff i).coeff j).totalDegree ≤ D

private lemma entry_degree (d D : ℕ) (f : (MvPolynomial τ K)[X][X])
    (hf : BivariateParameterDegreeBound f D) (i : ℕ × ℕ) (j : ClosedFormColumns d) :
    (closedFormCoefficientMatrix d f i j).totalDegree ≤ D := by
  rw [closedFormEntry_apply]; dsimp only
  rw [← map_intCast (MvPolynomial.C : K →+* MvPolynomial τ K)]
  exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_C,zero_add]; exact hf _ _)

end

variable {K τ ι : Type*} [CommRing K] (d r : ℕ) (f : (MvPolynomial τ K)[X][X]) (D : ℕ)
    (hf : BivariateParameterDegreeBound f D)

/-- If every entry of a square matrix of multivariate polynomials has total degree at most `D`, then
its determinant has total degree at most the size of the matrix times `D`. -/
lemma matrix_det_parameterDegree [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial τ K)) (D : ℕ)
    (hM : ∀ i j, (M i j).totalDegree ≤ D) :
    M.det.totalDegree ≤ Fintype.card ι * D := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s _
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc ∑ i, (M (s i) i).totalDegree ≤ ∑ _ : ι, D :=
      Finset.sum_le_sum (by grind)
    _ = _ := by simp

include hf in
/-- The parameter degree of any r-row minor is at most r times the coefficient
parameter degree; no dependence on the chosen row exponents is introduced. -/
theorem closedForm_minor_parameterDegree
    (a : Fin r → ℕ × ℕ) (c : Fin r → ClosedFormColumns d) :
    (((closedFormCoefficientMatrix d f).submatrix a c).det).totalDegree ≤ r * D := by
  simpa using matrix_det_parameterDegree ((closedFormCoefficientMatrix d f).submatrix a c) D (fun i j => entry_degree d D f hf (a i) (c j))

end
end CCDN
