/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.MonomialEvaluationMatrix
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Elementary determinant bounds

The archimedean Gram determinant estimate is the one used in CCDN §3.3. The row-factor
divisibility lemma isolates a basic arithmetic input to determinant lower bounds; it does not
assert the much stronger local multiplicity estimates of CCDN §2.
-/

@[expose] public section

namespace CCDN

open Matrix

/-- If row `i` is divisible by `d i`, the product of the row factors divides the determinant. -/
theorem prod_row_factors_dvd_det {R : Type*} [CommRing R] {s : ℕ}
    (A : Matrix (Fin s) (Fin s) R)
    (d : Fin s → R) (h : ∀ i j, d i ∣ A i j) : (∏ i, d i) ∣ A.det := by
  classical
  choose Q hQ using h
  have hA : A = Matrix.of (fun i j => d i * Q i j) := by
    aesop
  rw [hA]
  exact ⟨(Matrix.of Q).det, Matrix.det_mul_column d (Matrix.of Q)⟩

end CCDN
