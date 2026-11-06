
import GS.NonmanifoldCompletion.BlockExtraction




/-!
# Exact gauge normalization of every factor tuple above the scalar base matrix

The gauges are fixed diagonal sign matrices. Their values may depend on the
chosen point of the fibre; a continuous global choice on the whole fibre is
neither required nor asserted. This is suited to compact full-fibre coverage.

-/
open Matrix
namespace GS.NonmanifoldCompletion

variable (D E : Mat 2)

def DiagonalTwo  : Prop := D 0 1=0 ∧ D 1 0=0

theorem diagonalTwo_transpose {D : Mat 2} (hD : DiagonalTwo D) : DiagonalTwo Dᵀ :=
  ⟨hD.2,hD.1⟩

theorem diagonalTwo_symmetric (hD : DiagonalTwo D) : Dᵀ=D := by
  ext i j
  fin_cases i,j <;> simp_all [DiagonalTwo]

theorem diagonalTwo_mul {D E : Mat 2} (hD : DiagonalTwo D) (hE : DiagonalTwo E) :
    DiagonalTwo (D*E) := by
  constructor <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hD.1,hD.2,hE.1,hE.2]

theorem diagonalTwo_involution {D : Mat 2} (hd : DiagonalTwo D)
    (ho : Orthogonal D) : D*D=1 := by
  simpa only [diagonalTwo_symmetric D hd] using ho.1

theorem diagonalTwo_entry_sq {D : Mat 2} (hd : DiagonalTwo D)
    (ho : Orthogonal D) (a : Fin 2) : (D a a)^2=1 := by
  have h := congrFun (congrFun ho.1 a) a
  fin_cases a <;>
    simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,
      Fin.sum_univ_two,hd.1,hd.2,pow_two] using h

/-- A row-and-column gauge on a q-by-q middle factor. -/
def gaugeMiddle (D E : Fin q → Mat 2) (a : Fin 2) (A : Mat q) := Matrix.diagonal (fun i => D i a a) * A * Matrix.diagonal (fun j => E j a a)

@[simp] theorem gaugeMiddle_apply (D E : Fin q → Mat 2)
    (a : Fin 2) (A : Mat q) (i j : Fin q) :
    gaugeMiddle D E a A i j = D i a a * A i j * E j a a := by
  simp [gaugeMiddle,Matrix.mul_apply,Matrix.diagonal]

theorem signs_diagonal_orthogonal (s : Fin q → ℝ)
    (hs : ∀ i, (s i)^2=1) : Orthogonal (Matrix.diagonal s) := by
  constructor <;> rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  all_goals simp only [← pow_two, hs, Matrix.diagonal_one]

theorem gaugeMiddle_orthogonal (D E : Fin q → Mat 2)
    (hD : ∀ i, DiagonalTwo (D i) ∧ Orthogonal (D i))
    (hE : ∀ j, DiagonalTwo (E j) ∧ Orthogonal (E j))
    (a : Fin 2) (A : Mat q) (hA : Orthogonal A) : Orthogonal (gaugeMiddle D E a A) :=
  ((signs_diagonal_orthogonal _ (fun i => diagonalTwo_entry_sq (hD i).1 (hD i).2 a)).mul hA).mul
    (signs_diagonal_orthogonal _ (fun j => diagonalTwo_entry_sq (hE j).1 (hE j).2 a))

theorem diagonal_gauge_middle  (hD : DiagonalTwo D)
    (hE : DiagonalTwo E) (a b : ℝ) :
    D * diagTwo a b * E = diagTwo (D 0 0*a*E 0 0) (D 1 1*b*E 1 1) := by
  ext i j
  fin_cases i,j <;>
    simp [diagTwo,Matrix.mul_apply,Fin.sum_univ_two,hD.1,hD.2,hE.1,hE.2]

end GS.NonmanifoldCompletion
