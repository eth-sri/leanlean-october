module

public import HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Entrywise matrix contraction

This module defines the entrywise Frobenius contraction used by the
time--velocity operator and relates it to matrix trace when the second matrix
is symmetric.
-/

@[expose] public section

open scoped BigOperators

namespace HypoellipticAleksandrov

/-- The entrywise Frobenius contraction of two real square matrices. -/
def matrixContraction {d : ℕ} (A H : PDE.Mat d) : ℝ :=
  ∑ i, ∑ j, A i j * H i j

variable {d : ℕ}



/-- The contraction with a zero right factor vanishes. -/
@[simp]
theorem matrixContraction_zero_right  (A : PDE.Mat d) :
    matrixContraction A 0 = 0 := by
  simp [matrixContraction]

/-- The contraction is additive in its left factor. -/
@[simp]
theorem matrixContraction_add_left  (A B H : PDE.Mat d) :
    matrixContraction (A + B) H =
      matrixContraction A H + matrixContraction B H := by
  simp [matrixContraction, add_mul, Finset.sum_add_distrib]

/-- The contraction is additive in its right factor. -/
@[simp]
theorem matrixContraction_add_right  (A H K : PDE.Mat d) :
    matrixContraction A (H + K) =
      matrixContraction A H + matrixContraction A K := by
  simp [matrixContraction, mul_add, Finset.sum_add_distrib]

variable (c : ℝ) (A H : PDE.Mat d)

/-- The contraction is homogeneous in its left factor. -/
@[simp]
theorem matrixContraction_smul_left   :
    matrixContraction (c • A) H = c * matrixContraction A H := by
  simp [matrixContraction, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- The contraction is homogeneous in its right factor. -/
@[simp]
theorem matrixContraction_smul_right   :
    matrixContraction A (c • H) = c * matrixContraction A H := by
  simp [matrixContraction, smul_eq_mul, mul_left_comm, Finset.mul_sum]

variable (A H : PDE.Mat d)

/-- Negating the left factor negates the contraction. -/
@[simp]
theorem matrixContraction_neg_left   :
    matrixContraction (-A) H = -matrixContraction A H := by
  simp [matrixContraction]

/-- Negating the right factor negates the contraction. -/
@[simp]
theorem matrixContraction_neg_right   :
    matrixContraction A (-H) = -matrixContraction A H := by
  simp [matrixContraction]

/-- For a symmetric right factor, entrywise contraction equals the trace product. -/
theorem matrixContraction_eq_trace_mul_of_isSymm
     (hH : H.IsSymm) :
    matrixContraction A H = (A * H).trace := (id
  (Trans.trans
    (Finset.sum_congr rfl fun i _hi =>
      Finset.sum_congr rfl fun j _hj =>
        Eq.mpr (id (congrArg (fun _a => A i j * _a = A i j * H j i) (Matrix.IsSymm.apply hH j i)))
          (Eq.refl (A i j * H j i)))
    rfl))

end HypoellipticAleksandrov
