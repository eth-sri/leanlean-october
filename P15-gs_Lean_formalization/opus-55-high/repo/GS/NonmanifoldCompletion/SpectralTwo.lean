module

public import GS.Continuation.ExponentialBasics
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section


/-!
# A real orthogonal diagonalizer for the original two-by-two middle block

The result is an existence theorem, not a continuous choice of eigenvectors.
The exceptional point u=(-1,0) is handled explicitly.  No angle, logarithm,
local-coverage hypothesis, or topological nonmanifold assertion is assumed.

-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
namespace GS.NonmanifoldCompletion

/-- Diagonal two-by-two matrix, with the order of eigenvalues fixed. -/
def diagTwo {R : Type*} [Zero R] (a b : R) : Matrix (Fin 2) (Fin 2) R := diagonal ![a,b]

/-- Algebraic half-angle representatives. Only existence is asserted. -/
theorem exists_half_coordinates (u : CircleVector) (hu : OnCircle u) :
    ∃ c s : ℝ, c^2+s^2=1 ∧ c^2-s^2=u 0 ∧ 2*c*s=u 1 := by
  have hu' : u 0^2+u 1^2=1 := hu
  by_cases hx : u 0 = -1
  · grind
  · have hlow : -1 ≤ u 0 := by
      nlinarith
    let r := Real.sqrt (2*(1+u 0))
    refine ⟨(1+u 0)/r,u 1/r,?_,?_,?_⟩
    · grind
    · grind
    grind

theorem diagTwo_scalar (a b : ℝ) :
    diagTwo a b = ((a+b)/2) • (1 : Mat 2) +
      ((a-b)/2) • diagTwo 1 (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagTwo] <;> ring

/-- A common orthogonal diagonalizer works for ALL scalar pairs a,b. -/
theorem exists_common_middle_diagonalizer (u : CircleVector) (hu : OnCircle u) :
    ∃ S : Mat 2, Orthogonal S ∧
      ∀ a b : ℝ, middleBlock a b u = S * diagTwo a b * Sᵀ := by
  obtain ⟨c,s,hunit,hdiff,hprod⟩ := exists_half_coordinates u hu
  let v := ![c,s]
  let S := T v
  have hv := hunit
  have hS : Orthogonal S := T_orthogonal hv
  have hconj : S * diagTwo 1 (-1) * Sᵀ = T u := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S,v,T,diagTwo,vecMul_diagonal,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two] <;>
      nlinarith [hdiff,hprod]
  refine ⟨S,hS,?_⟩
  intro a b
  rw [diagTwo_scalar]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hS.2, hconj]
  rfl

end GS.NonmanifoldCompletion
