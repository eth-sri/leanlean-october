module

public import GS.Extensions.OriginalCompact
public import GS.Extensions.MatrixCalculus
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Matrix exponential: structure, orthogonality and actual scalar derivatives

 The exponential is the existing
GS.matrixExp power series, not a new opaque solution of an ODE.

Derivative proofs first export scalar coordinate derivatives from the auxiliary
operator norm and then reconstruct the matrix derivative in its default product
norm. No Frobenius/default/operator norm identification is used.
-/

noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace GS.Continuation
open GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem supported_pow {block : Fin n → ℕ} {A : Mat n}
    (hA : Supported block A) (k : ℕ) : Supported block (A ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => simpa only [pow_succ] using ih.mul hA

/-- Powers and finite sums have the same block support; its closedness passes
that property to the convergent matrix-exponential series. -/
theorem supported_matrixExp {block : Fin n → ℕ} {A : Mat n}
    (hA : Supported block A) : Supported block (matrixExp A) :=
  (isClosed_supported n block).mem_of_tendsto (matrixExp_hasSum A) (.of_forall fun _ =>
    Finset.sum_induction _ (Supported block) (fun _ _ => .add) .zero fun k _ => .smul _ (supported_pow hA k))

/-- Transposition commutes with the actual power-series exponential. -/
theorem matrixExp_transpose (A : Mat n) : matrixExp (Aᵀ) = (matrixExp A)ᵀ := by
  simpa only [matrixExp_eq_exp] using Matrix.exp_transpose A

section
variable (A : Mat n)
theorem matrixExp_neg_mul : matrixExp (-A) * matrixExp A = 1 := by
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Mat n) := Matrix.linftyOpNormedAlgebra
  simpa [matrixExp_eq_exp] using (NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl A))).symm

theorem matrixExp_mul_neg : matrixExp A * matrixExp (-A) = 1 := by
  simpa only [neg_neg] using matrixExp_neg_mul (-A)

end

/-- Orthogonality of exp(skew) is a theorem, not an ODE hypothesis. -/
theorem matrixExp_orthogonal {A : Mat n} (hA : IsSkew A) :
    Orthogonal (matrixExp A) := by
  apply Orthogonal.of_transpose_mul
  rw [← matrixExp_transpose, hA]
  exact matrixExp_neg_mul A

theorem isSkew_smul (t : ℝ) {A : Mat n} (hA : IsSkew A) : IsSkew (t • A) := by
  simp_all [IsSkew]

/-- A named, concrete exponential line. -/
def expLine (C : Mat n) (t : ℝ) : Mat n := matrixExp (t • C)


theorem expLine_supported {block : Fin n → ℕ} {C : Mat n}
    (hC : Supported block C) (t : ℝ) : Supported block (expLine C t) :=
  supported_matrixExp (Supported.smul t hC)

theorem expLine_orthogonal {C : Mat n} (hC : IsSkew C) (t : ℝ) :
    Orthogonal (expLine C t) := matrixExp_orthogonal (isSkew_smul t hC)

section
variable (C : Mat n) (t : ℝ)
theorem hasDerivAt_expLine :
    HasDerivAt (expLine C) (expLine C t * C) t ∧ HasDerivAt (expLine C) (C * expLine C t) t := by
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  have h₁ := hasDerivAt_exp_smul_const (𝕂 := ℝ) C t
  have h₂ := hasDerivAt_exp_smul_const' (𝕂 := ℝ) C t
  constructor <;> refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_ <;>
  · let ev : Mat n →L[ℝ] ℝ := { toFun A := A i j, map_add' := by simp, map_smul' := by simp, cont := by fun_prop }
    first
    | simpa [expLine, matrixExp_eq_exp, ev, Function.comp_def] using ev.hasFDerivAt.comp_hasDerivAt t h₁
    | simpa [expLine, matrixExp_eq_exp, ev, Function.comp_def] using ev.hasFDerivAt.comp_hasDerivAt t h₂

end

end GS.Continuation
