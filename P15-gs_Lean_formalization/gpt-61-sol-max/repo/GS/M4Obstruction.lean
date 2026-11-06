
import GS.M4Certificate



/-! The computed matrix violates the actual determinant inequality.
A proof script for necessity is supplied separately in M4Necessary.lean.
 -/

noncomputable section
namespace GS.M4

def root6 : ℝ := Real.sqrt 2 * Real.sqrt 3

theorem root6_pos : 0 < root6 := by
  unfold root6; positivity

theorem root6_sq : root6^2 = 6 := by
  norm_num [root6,mul_pow]

variable (A : Mat 6)

def absDetBlock  (i j : Fin 3) : ℝ := |detBlock A i j|

def absDetTable := !![3*root6/16, 1/8, 3/8;
     3*root6/16, 3/8, 1/8;
     1/16, 3*root6/16, 3*root6/16]

theorem absDetTable_Q : absDetBlock Q = absDetTable := by
  ext i j
  have hd := congrFun (congrFun detTable_Q i) j
  unfold absDetBlock
  rw [hd]
  fin_cases i,j <;>
    simp [detTable,absDetTable,root6,abs_mul,abs_div,
      abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ)),
      abs_of_nonneg (Real.sqrt_nonneg (3 : ℝ))] <;> ring

def determinantObstruction  : Prop :=
  let d := absDetBlock A
  (1-d 0 2*d 1 0/d 2 1)*(1-d 0 2*d 2 1/d 1 0) ≥ d 0 0*d 2 2/d 1 1

theorem obstruction_denominator_nonzero :
    absDetBlock Q 2 1 * absDetBlock Q 1 0 * absDetBlock Q 1 1 ≠ 0 := by
  rw [absDetTable_Q]
  have := root6_pos
  dsimp [absDetTable]
  positivity

theorem Q_violates_determinantObstruction : ¬ determinantObstruction Q := by
  have hr := root6_sq
  have ht := ne_of_gt root6_pos
  norm_num [determinantObstruction,absDetTable_Q,absDetTable]
  field_simp [ht]
  nlinarith

end GS.M4
