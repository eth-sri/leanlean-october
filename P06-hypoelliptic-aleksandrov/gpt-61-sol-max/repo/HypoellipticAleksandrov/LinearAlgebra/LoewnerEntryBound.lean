module

public import HypoellipticAleksandrov.Coefficients.Ellipticity

/-!
# Entry bounds from Loewner bounds

This module extracts a uniform coordinate bound from two-sided Loewner control.
-/

 public section

open scoped MatrixOrder

namespace HypoellipticAleksandrov

/-- Entries of a matrix with `0 ≤ A ≤ Λ I` are bounded by `Λ`. -/
theorem abs_apply_le_of_posSemidef_upper {n : ℕ} {A : PDE.Mat n} {Lam : ℝ} (h0 : A.PosSemidef)
    (h1 : (Lam • (1 : PDE.Mat n) - A).PosSemidef) (i j : Fin n) : |A i j| ≤ Lam := by
  have hdiag (k : Fin n) : A k k ≤ Lam := by
    simpa [Matrix.sub_apply, Matrix.smul_apply] using h1.diag_nonneg (i := k)
  have hsymm : A j i = A i j := by simpa using h0.isHermitian.apply i j
  have h (s : ℝ) := h0.dotProduct_mulVec_nonneg (Pi.single i (1 : ℝ) + Pi.single j s)
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_single, dotProduct_add,
    add_dotProduct, single_dotProduct, Pi.smul_apply, Matrix.col_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, hsymm] at h
  rw [abs_le]
  constructor <;> nlinarith [h 1, h (-1), hdiag i, hdiag j]

/-- A positive lower Loewner bound and a scalar upper Loewner bound control
every matrix entry by the upper scalar. -/
theorem abs_apply_le_of_loewner
    {d : ℕ} {lam Lam : ℝ} {A : PDE.Mat d}
    (hlam : 0 < lam)
    (hlower : lam • (1 : PDE.Mat d) ≤ A)
    (hupper : A ≤ Lam • (1 : PDE.Mat d))
    (i j : Fin d) :
    |A i j| ≤ Lam :=
  abs_apply_le_of_posSemidef_upper
    (posDef_of_loewner_lower hlam hlower).posSemidef (Matrix.le_iff.mp hupper) i j


end HypoellipticAleksandrov
