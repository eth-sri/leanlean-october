
import GS.Continuation.ExponentialBasics
import GS.MatrixCS.ColumnGram
import Mathlib.Analysis.SpecialFunctions.Sqrt



/-!
# A real orthogonal diagonalizer for the original two-by-two middle block

The result is an existence theorem, not a continuous choice of eigenvectors.
The exceptional point u=(-1,0) is handled explicitly.  No angle, logarithm,
local-coverage hypothesis, or topological nonmanifold assertion is assumed.

-/
open Matrix
namespace GS.NonmanifoldCompletion

variable (a b : ℝ)

/-- Diagonal two-by-two matrix, with the order of eigenvalues fixed. -/
def diagTwo  : Mat 2 := !![a, 0; 0, b]

theorem diagTwo_scalar  :
    diagTwo a b = ((a+b)/2) • (1 : Mat 2) +
      ((a-b)/2) • diagTwo 1 (-1) := by
  ext i j
  fin_cases i,j <;>
    simp [diagTwo] <;> ring

/-- A common orthogonal diagonalizer works for ALL scalar pairs a,b. -/
theorem exists_common_middle_diagonalizer (u : CircleVector) (hu : OnCircle u) :
    ∃ S : Mat 2, Orthogonal S ∧
      ∀ a b : ℝ, middleBlock a b u = S * diagTwo a b * Sᵀ := by
  have hD : (diagTwo 1 (-1)).IsHermitian := by
    
    ext i j
    fin_cases i,j <;> rfl
  have hd : (T u).det = -1 := by
    dsimp [OnCircle] at hu
    simp [T, Matrix.det_fin_two]
    nlinarith [hu]
  have hc : (diagTwo 1 (-1)).charpoly = (T u).charpoly := by
    rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two, hd]
    norm_num [diagTwo, T, Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two]
  obtain ⟨U,hU,he⟩ := GS.MatrixCS.exists_unitary_conjugation hD (T_transpose u) hc
  let S := Uᵀ
  have hS : Orthogonal S := hU.conjTranspose
  have hconj : S * diagTwo 1 (-1) * Sᵀ = T u := he
  refine ⟨S,hS,?_⟩
  intro a b
  rw [diagTwo_scalar]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hS.2, hconj]
  rfl

end GS.NonmanifoldCompletion
