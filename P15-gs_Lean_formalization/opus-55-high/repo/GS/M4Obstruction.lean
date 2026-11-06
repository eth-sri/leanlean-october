module

public import GS.M4Certificate

@[expose] public section


/-! The computed matrix violates the actual determinant inequality.
A proof script for necessity is supplied separately in M4Necessary.lean.
 -/

noncomputable section
namespace GS.M4

def root6 : ℝ := Real.sqrt 2 * Real.sqrt 3

def absDetBlock (A : Mat 6) (i j : Fin 3) : ℝ := |detBlock A i j|

def absDetTable : Mat 3 :=
  !![3*root6/16, 1/8, 3/8;
     3*root6/16, 3/8, 1/8;
     1/16, 3*root6/16, 3*root6/16]

theorem absDetTable_Q : absDetBlock Q = absDetTable := by
  ext i j
  rw [absDetBlock, congrFun₂ detTable_Q i j]
  fin_cases i <;> fin_cases j <;>
    simp [detTable,absDetTable,root6,abs_mul,abs_div,
      abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ)),
      abs_of_nonneg (Real.sqrt_nonneg (3 : ℝ))] <;> ring

/-- Scalar end of the necessity proof, after the block determinants have been
expressed in terms of absolute matrix entries. -/
theorem scalar_obstruction (a b e f c g : ℝ)
    (ha : a^2+c^2=1) (he : e^2+g^2=1) (hb : b^2 ≤ 1) (hf : f^2 ≤ 1) :
    (1-b^2*e^2)*(1-a^2*f^2) ≥ c^2*g^2 := by
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg e) (sub_nonneg.mpr hb)) (show 0 ≤ 1-a^2*f^2 by nlinarith),
    mul_nonneg (mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hf)) (show (0:ℝ) ≤ 1-e^2 by nlinarith)]

end GS.M4
