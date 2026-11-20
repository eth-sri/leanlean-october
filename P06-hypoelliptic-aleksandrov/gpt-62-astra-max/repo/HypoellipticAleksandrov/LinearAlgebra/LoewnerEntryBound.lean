module

public import HypoellipticAleksandrov.Coefficients.Ellipticity

/-!
# Entry bounds from Loewner bounds

This module extracts a uniform coordinate bound from two-sided Loewner control.
-/

@[expose] public section

open scoped MatrixOrder

namespace HypoellipticAleksandrov

/-- A positive lower Loewner bound and a scalar upper Loewner bound control
every matrix entry by the upper scalar. -/
theorem abs_apply_le_of_loewner
    {d : ℕ} {lam Lam : ℝ} {A : PDE.Mat d}
    (hlam : 0 < lam)
    (hlower : lam • (1 : PDE.Mat d) ≤ A)
    (hupper : A ≤ Lam • (1 : PDE.Mat d))
    (i j : Fin d) :
    |A i j| ≤ Lam := by
  classical
  have hA : A.PosSemidef := (posDef_of_loewner_lower hlam hlower).posSemidef
  have hgap := Matrix.le_iff.mp hupper
  have hsymm : A i j = A j i := by
    exact (hA.isHermitian.apply i j).symm
  have hii_upper : A i i ≤ Lam := by
    have := hgap.diag_nonneg (i := i)
    simpa using this
  have hjj_upper : A j j ≤ Lam := by
    have := hgap.diag_nonneg (i := j)
    simpa using this
  by_cases hij : i = j
  · subst j
    rw [abs_of_nonneg hA.diag_nonneg]
    exact hii_upper
  · have hplus := hA.dotProduct_mulVec_nonneg
        ((Pi.single i 1 + Pi.single j 1))
    have hminus := hA.dotProduct_mulVec_nonneg
        ((Pi.single i 1 - Pi.single j 1))
    have hplus' : 0 ≤ A i i + A i j + A j i + A j j := by
      have h : 0 ≤ A i i + A i j + (A j i + A j j) := by
        simpa [Matrix.mulVec] using hplus
      linarith
    have hminus' : 0 ≤ A i i - A i j - A j i + A j j := by
      have h : A j i ≤ A i i - A i j + A j j := by
        simpa [Matrix.mulVec] using hminus
      linarith
    grind

end HypoellipticAleksandrov
