
import GS.Extensions.OriginalCompact
import GS.Extensions.MatrixCalculus
import Mathlib.Analysis.SpecialFunctions.Exponential



/-!
# Matrix exponential: structure, orthogonality and actual scalar derivatives

 The exponential is the existing
standard matrix exponential power series, not a new opaque solution of an ODE.

Derivative proofs first export scalar coordinate derivatives from the auxiliary
operator norm and then reconstruct the matrix derivative in its default product
norm. No Frobenius/default/operator norm identification is used.
-/

noncomputable section
open Matrix
namespace GS.Continuation

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace






variable (A C : Mat n)

variable (t : ℝ)

theorem matrixExp_orthogonal {A : Mat n} (hA : IsSkew A) :
    Orthogonal (NormedSpace.exp A) := by
  apply Orthogonal.of_transpose_mul
  rw [← Matrix.exp_transpose,hA,← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_left]
  simp

theorem isSkew_smul  {A : Mat n} (hA : IsSkew A) : IsSkew (t • A) := by
  change (t • A)ᵀ = -(t • A)
  rw [Matrix.transpose_smul, hA, smul_neg]

/-- A named, concrete exponential line. -/
def expLine   : Mat n := NormedSpace.exp (t • C)









attribute [-instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem hasDerivAt_expLine   :
    HasDerivAt (expLine C) (expLine C t * C) t := by
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  
  simpa only [expLine] using!
    hasDerivAt_exp_smul_const  C t

theorem hasDerivAt_expLine_left   :
    HasDerivAt (expLine C) (C * expLine C t) t := by
  have h : Commute C (expLine C t) := by
    simpa only [expLine] using ((Commute.refl C).smul_right t).exp_right
  simpa only [h.eq] using hasDerivAt_expLine C t

end GS.Continuation
