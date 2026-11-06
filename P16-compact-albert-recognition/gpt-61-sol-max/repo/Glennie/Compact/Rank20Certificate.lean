/- The flat Jacobian is a rational matrix with each column rescaled by
   either 1 or sqrt 3.  Rational row elimination certifies nonsingularity. -/
module
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section
namespace Glennie.Compact.Rank20Certificate
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def J0 : Matrix (Fin 20) (Fin 20) ℝ := fun i j =>
  let a : Fin 3 := ⟨i.val / 8, by omega⟩
  let r : Fin 8 := ![0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,3,4] i
  let slot : Fin 4 := ![0,0,1,1,2,2,1,1,0,0,2,2,1,1,0,0,3,3,3,3] j
  (!![0,1,1,1;1,0,-1,1;-1,-1,0,0] : Matrix (Fin 3) (Fin 4) ℝ) a slot *
    (let c : Fin 8 := ![0,1,1,0,2,3,4,5,6,7,6,7,3,2,5,4,4,5,6,7] j
     let k : ℝ := ![2,2,-1,-1,1,1,1,1,2,2,1,1,1,-1,-2,2,-1,-1,-2,-2] j
     k * (!![-2, -2, -2, 2, 1, -1, -2, 0;
    -2, -2, 4, 0, -1, -1, 1, 1;
    -2, -2, -2, -2, 0, 2, 1, -1;
    0, 4, -2, 2, -1, -1, 1, -1;
    0, 4, 4, 0, 0, 2, -2, 0;
    0, 4, -2, -2, 1, -1, 1, 1;
    2, -2, -2, 2, 0, 2, 1, 1;
    2, -2, 4, 0, 1, -1, 1, -1] : Matrix (Fin 8) (Fin 8) ℝ) r c)

def columnScale (j : Fin 20) : ℝ :=
  if j.val ∈ [0,3,5,6,9,11,12,15,16,19] then Real.sqrt 3 else 1

def JQ : Matrix (Fin 20) (Fin 20) ℝ := fun i j => J0 i j * columnScale j / 72

theorem det_J0_ne_zero : J0.det ≠ 0 := by
  suffices H : LinearIndependent ℝ J0.row from
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp H)).ne_zero
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h : ∀ k, ∑ j, c j * J0 j k = 0 := by
    intro k
    have h := congrArg (fun v => v k) hc
    exact h
  simp only [Fin.forall_fin_succ] at h
  norm_num [J0, Fin.sum_univ_succ] at h
  fin_cases i <;> dsimp only <;> linarith! only [h]

theorem det_JQ_ne_zero : JQ.det ≠ 0 := by
  have hQ : JQ = (72 : ℝ)⁻¹ • (J0 * Matrix.diagonal columnScale) := by
    ext i j
    simp only [JQ, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hQ, Matrix.det_smul, Matrix.det_mul, Matrix.det_diagonal]
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero det_J0_ne_zero ?_)
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  fin_cases i <;> norm_num [columnScale]

end
end Glennie.Compact.Rank20Certificate
