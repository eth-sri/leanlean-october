module

public import GS.UnitaryLocalModel.PauliCoordinates

@[expose] public section


/-! Exact unitary diagonalization of every Pauli axis, including both poles.
Only existence is asserted: a globally continuous choice is neither used nor
assumed. The simultaneous conjugation formula holds for every pair of scalars. -/
noncomputable section
open GS Matrix GS.UnitaryGeometry GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel

theorem conjugated_diagTwo_eq_middle (S : CMat 2) (hS : GS.Unitary S)
    (u : AxisVector) (he : Sᴴ*diagTwo 1 (-1)*S = pauli u) (a b : ℂ) :
    Sᴴ*diagTwo a b*S = middleBlock a b u := by
  rw [show diagTwo a b = ((a+b)/2) • (1 : CMat 2) + ((a-b)/2) • diagTwo 1 (-1) by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diagTwo] <;> ring]
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,hS.1,he,middleBlock]

theorem exists_axis_of_unitary (S : CMat 2) (hS : GS.Unitary S) :
    ∃ u : AxisVector, OnSphere u ∧
      ∀ a b : ℂ, Sᴴ*diagTwo a b*S = middleBlock a b u := by
  obtain ⟨hZ, hZ2⟩ : (diagTwo 1 (-1) : CMat 2)ᴴ = diagTwo 1 (-1) ∧ diagTwo 1 (-1) * diagTwo 1 (-1) = (1 : CMat 2) := by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [diagTwo]
  obtain ⟨u,hu,he⟩ := exists_sphere_pauli (Sᴴ*diagTwo 1 (-1)*S)
    (by simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hZ,Matrix.mul_assoc])
    (by rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,hS.2,Matrix.one_mul]; simp [diagTwo, Matrix.trace])
    (by simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc S, hS.2, Matrix.one_mul, ← Matrix.mul_assoc (diagTwo 1 (-1)), hZ2, Matrix.one_mul, hS.1])
  exact ⟨u,hu,conjugated_diagTwo_eq_middle S hS u he.symm⟩

/-- Every axis admits a unitary diagonalizer. The antipodal pole is handled
explicitly, so no denominator is silently assumed nonzero. -/
theorem middleBlock_unitary_diagonalization (u : AxisVector) (hu : OnSphere u) :
    ∃ S : CMat 2, GS.Unitary S ∧
      ∀ a b : ℂ, Sᴴ*diagTwo a b*S = middleBlock a b u := by
  suffices ∃ S : CMat 2, GS.Unitary S ∧ Sᴴ*diagTwo 1 (-1)*S = pauli u by
    obtain ⟨S,hS,he⟩ := this
    exact ⟨S,hS,conjugated_diagTwo_eq_middle S hS u he⟩
  unfold OnSphere at hu
  by_cases hp : u 0 = -1
  · obtain ⟨h1, h2⟩ : u 1 = 0 ∧ u 2 = 0 := by constructor <;> nlinarith
    refine ⟨!![0,1;1,0],⟨?_,?_⟩,?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [diagTwo,pauli,hp,h1,h2,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply]
  have h0 : 0 < 2*(1+u 0) := by linarith [lt_of_le_of_ne (show -1 ≤ u 0 by nlinarith) (Ne.symm hp)]
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ r^2 = 2*(1+u 0) := ⟨_, Real.sqrt_pos.2 h0, Real.sq_sqrt h0.le⟩
  refine ⟨.of fun i j => ((r⁻¹ : ℝ) : ℂ) * ![![((1+u 0 : ℝ) : ℂ), u 1 - Complex.I * u 2],
    ![-(u 1 + Complex.I * u 2), ((1+u 0 : ℝ) : ℂ)]] i j, ⟨?_, ?_⟩, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Complex.ext_iff, Matrix.mul_apply, Fin.sum_univ_two, pauli, diagTwo] <;> field_simp
  all_goals rw [hr]; constructor <;> linarith

end GS.UnitaryLocalModel
