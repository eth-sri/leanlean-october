/- Explicit inverse of the selected native word-coordinate matrix. -/
module
public import Glennie.Compact.NativeWordTableCoordinatesR01
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix

def coordinateMatrix : Matrix (Fin 27) (Fin 27) ℝ := fun i j => columns j i

def inverseMatrix : Matrix (Fin 27) (Fin 27) ℝ := ![
![0, 1, 0, 0, -2, (4/3), 0, (-4/3), 0, 0, -2, 2, 0, 0, (-4/3), 0, 2, (-4/3), 0, 0, -2, 2, 0, (4/3), 0, 0, (-4/3)],
![(-1/2), 0, (1/2), 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, 0, (-2/3), 0, (-2/3), 0, 0, 0, 1, (2/3), 0, 0, 0, 0, (-2/3), 0, 0, 0, 0, 0, (-2/3), (-2/3), 0],
![0, 0, 0, 0, 0, 0, (1/3), 0, (-1/3), 0, 0, 0, 0, (1/3), 0, -1, 0, 0, (1/3), 0, 0, 0, 0, 0, (1/3), (-1/3), 0],
![(1/2), -1, (1/2), 0, 2, 0, 0, 0, 0, 0, 2, -4, 0, 0, 0, 0, -4, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0],
![0, 0, 0, -1, 0, 0, 4, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 1, 0, 0, 0, 0, 0, -4, 0],
![0, 0, 0, 0, 0, 0, -1, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, -1, 0],
![0, 0, 0, 0, 1, (-2/3), 0, (2/3), 0, 0, 0, -1, 0, 0, (2/3), 0, 0, (2/3), 0, 0, 1, 0, 0, (-2/3), 0, 0, (2/3)],
![0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0],
![0, 0, 0, 0, 0, (-2/3), 0, (2/3), 0, 0, 1, 0, 0, 0, (2/3), 0, -1, (2/3), 0, 0, 0, -1, 0, (-2/3), 0, 0, (2/3)],
![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0],
![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, (2/3), 0, (4/3), 0, 0, 0, 0, 0, 0, (-2/3), 0, 0, (-2/3), 0, 0, 0, 0, 0, (-4/3), 0, 0, (-2/3)],
![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, (-2/3), 0, (2/3), 0, 0, 0, 0, 0, 0, (-4/3), 0, 0, (-4/3), 0, 0, 0, 0, 0, (-2/3), 0, 0, (2/3)],
![0, 0, 0, 0, 0, 0, (-2/3), 0, (2/3), 0, 0, 0, 0, (-2/3), 0, 0, 0, 0, (-2/3), 0, 0, 0, 0, 0, (-2/3), (2/3), 0],
![0, 0, 0, 0, 0, 0, (1/3), 0, (1/3), 0, 0, 0, 0, (-1/3), 0, 0, 0, 0, (1/3), 0, 0, 0, 0, 0, (1/3), (1/3), 0],
![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0],
![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, 0, (-4/3), 0, (-4/3), 0, 0, 0, 0, (-8/3), 0, 0, 0, 0, (8/3), 0, 0, 0, 0, 0, (-4/3), (-4/3), 0],
![0, 0, 0, 0, 0, 0, (-2/3), 0, (2/3), 0, 0, 0, 0, (4/3), 0, 0, 0, 0, (4/3), 0, 0, 0, 0, 0, (-2/3), (2/3), 0],
![0, 0, 0, 0, 0, (1/3), 0, (-1/3), 0, 0, 0, 0, 0, 0, (-1/3), 0, 0, (-1/3), 0, 0, 0, 0, 0, (1/3), 0, 0, (-1/3)],
![0, 0, 0, 0, 0, 4, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 4],
![0, 0, 0, 0, 0, 0, (4/3), 0, (-8/3), 0, 0, 0, 0, (-4/3), 0, 0, 0, 0, (4/3), 0, 0, 0, 0, 0, (-8/3), (4/3), 0],
![0, 0, 0, 0, 0, 0, (-4/3), 0, (-2/3), 0, 0, 0, 0, (2/3), 0, 0, 0, 0, (2/3), 0, 0, 0, 0, 0, (2/3), (4/3), 0]
]



def Row (i : Fin 27) : Prop := ∀ j, (inverseMatrix * coordinateMatrix) i j = (1 : Matrix (Fin 27) (Fin 27) ℝ) i j

macro "lrow" : tactic => `(tactic| (intro j; rw [Matrix.mul_apply, Matrix.one_apply]; fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]))

theorem r0 : Row 0 := by lrow
theorem r1 : Row 1 := by lrow
theorem r2 : Row 2 := by lrow
theorem r3 : Row 3 := by lrow
theorem r4 : Row 4 := by lrow
theorem r5 : Row 5 := by lrow
theorem r6 : Row 6 := by lrow
theorem r7 : Row 7 := by lrow
theorem r8 : Row 8 := by lrow
theorem r9 : Row 9 := by lrow
theorem r10 : Row 10 := by lrow
theorem r11 : Row 11 := by lrow
theorem r12 : Row 12 := by lrow
theorem r13 : Row 13 := by lrow
theorem r14 : Row 14 := by lrow
theorem r15 : Row 15 := by lrow
theorem r16 : Row 16 := by lrow
theorem r17 : Row 17 := by lrow
theorem r18 : Row 18 := by lrow
theorem r19 : Row 19 := by lrow
theorem r20 : Row 20 := by lrow
theorem r21 : Row 21 := by lrow
theorem r22 : Row 22 := by lrow
theorem r23 : Row 23 := by lrow
theorem r24 : Row 24 := by lrow
theorem r25 : Row 25 := by lrow
theorem r26 : Row 26 := by lrow

theorem left_inverse : inverseMatrix * coordinateMatrix = 1 := by
  ext i j
  fin_cases i
  exacts [r0 j, r1 j, r2 j, r3 j, r4 j, r5 j, r6 j, r7 j, r8 j, r9 j, r10 j, r11 j, r12 j, r13 j, r14 j, r15 j, r16 j, r17 j, r18 j, r19 j, r20 j, r21 j, r22 j, r23 j, r24 j, r25 j, r26 j]

theorem right_inverse : coordinateMatrix * inverseMatrix = 1 :=
  mul_eq_one_comm.mp left_inverse

end
end Glennie.Compact.NativeWordTableR01
