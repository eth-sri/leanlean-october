
import GS.UnitaryLocalModel.PauliCoordinates
import GS.MatrixCS.ColumnGram



/-! Exact unitary diagonalization of every Pauli axis, including both poles.
Only existence is asserted: a globally continuous choice is neither used nor
assumed. The simultaneous conjugation formula holds for every pair of scalars. -/
open Matrix GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel

def axisDiagonal := diagTwo 1 (-1)

@[simp] theorem axisDiagonal_conjTranspose : axisDiagonalᴴ = axisDiagonal := by simp_all [axisDiagonal,diagTwo]

@[simp] theorem axisDiagonal_square : axisDiagonal*axisDiagonal = 1 := by
  ext i j
  fin_cases i,j <;> norm_num [axisDiagonal,diagTwo,Matrix.mul_apply,Fin.sum_univ_two]

@[simp] theorem axisDiagonal_trace : Matrix.trace axisDiagonal = 0 := by
  simp [axisDiagonal,diagTwo,Matrix.trace,Fin.sum_univ_two]

variable (S : CMat 2)

variable (u : AxisVector)

theorem conjugated_diagTwo_eq_middle  (hS : GS.Unitary S)
    (u : AxisVector) (he : Sᴴ*axisDiagonal*S = pauli u) (a b : ℂ) :
    Sᴴ*diagTwo a b*S = middleBlock a b u := by
  have hd : diagTwo a b = ((a+b)/2) • (1 : CMat 2) + ((a-b)/2) • axisDiagonal := by
    ext i j
    fin_cases i,j <;> simp [axisDiagonal,diagTwo] <;> ring
  rw [hd]
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,hS.1,he,middleBlock]

theorem exists_axis_of_unitary  (hS : GS.Unitary S) :
    ∃ u : AxisVector, OnSphere u ∧
      ∀ a b : ℂ, Sᴴ*diagTwo a b*S = middleBlock a b u := by
  let H := Sᴴ*axisDiagonal*S
  have hh : Hᴴ = H := by grind [axisDiagonal_conjTranspose,Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_mul]
  have ht : Matrix.trace H = 0 := by
    
    rw [Matrix.trace_mul_comm]
    rw [← Matrix.mul_assoc,hS.2,Matrix.one_mul,axisDiagonal_trace]
  have hs : H*H = 1 := by
    calc
      H*H = Sᴴ*axisDiagonal*(S*Sᴴ)*axisDiagonal*S := by grind
      _ = 1 := by rw [hS.2,Matrix.mul_one,Matrix.mul_assoc Sᴴ,axisDiagonal_square,
        Matrix.mul_one,hS.1]
  obtain ⟨u,hu,he⟩ := exists_sphere_pauli H hh ht hs
  exact ⟨u,hu,conjugated_diagTwo_eq_middle S hS u he.symm⟩

/-- Every axis admits a unitary diagonalizer. The antipodal pole is handled
explicitly, so no denominator is silently assumed nonzero. -/
theorem exists_unitary_for_axis  (hu : OnSphere u) :
    ∃ S : CMat 2, GS.Unitary S ∧ Sᴴ*axisDiagonal*S = pauli u := by
  have hd : (pauli u).det = -1 := by
    dsimp [OnSphere] at hu
    apply Complex.ext <;>
      simp [pauli, Matrix.det_fin_two, Complex.mul_re, Complex.mul_im] <;> nlinarith [hu]
  have hc : (pauli u).charpoly = axisDiagonal.charpoly := by simp_all [axisDiagonal,pauli,diagTwo,Fin.sum_univ_two,Matrix.charpoly_fin_two,Matrix.det_fin_two,Matrix.trace]
  exact GS.MatrixCS.exists_unitary_conjugation axisDiagonal_conjTranspose
    (pauli_conjTranspose u) hc.symm

/-- Every point of the sphere yields a simultaneous unitary middle factor. -/
theorem middleBlock_unitary_diagonalization  (hu : OnSphere u) :
    ∃ S : CMat 2, GS.Unitary S ∧
      ∀ a b : ℂ, Sᴴ*diagTwo a b*S = middleBlock a b u := by
  grind [conjugated_diagTwo_eq_middle, exists_unitary_for_axis]

end GS.UnitaryLocalModel
