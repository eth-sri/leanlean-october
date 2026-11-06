module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovarianceBoundsTrace
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoff
import Mathlib.Tactic

/-! # Native matrix contractions and ellipticity bounds for the Gaussian sign -/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Matrix
open scoped BigOperators MatrixOrder

variable {d : ℕ} (A : PDE.Mat d) (p : PDE.Vec d)

/-- Native rank-one contraction is the corresponding Euclidean quadratic form. -/
theorem matrixContraction_rankOne  :
    matrixContraction A (fun i j => p i * p j) = PDE.vecDot p (A.mulVec p) := by
  unfold matrixContraction PDE.vecDot Matrix.mulVec dotProduct
  simp only [Finset.mul_sum]
  grind

/-- Contraction against the identity is exactly the native matrix trace. -/
theorem matrixContraction_identity  :
    matrixContraction A (1 : PDE.Mat d) = A.trace := by
  simp [matrixContraction, Matrix.trace, Matrix.one_apply]

/-- The exact Gaussian Hessian contraction in native Euclidean coordinates. -/
theorem matrixContraction_gaussian  (a R : ℝ) :
    matrixContraction A (fun i j => a * (4 * p i * p j - 2 * R * (1 : PDE.Mat d) i j)) =
      a * (4 * PDE.vecDot p (A.mulVec p) - 2 * R * A.trace) := by
  let K : PDE.Mat d := fun i j => p i * p j
  have hm : (fun i j => a * (4 * p i * p j - 2 * R * (1 : PDE.Mat d) i j)) =
      a • ((4 : ℝ) • K + (-2 * R) • (1 : PDE.Mat d)) := by
    ext i j
    change a * (4 * p i * p j - 2 * R * (1 : PDE.Mat d) i j) =
      a * ((4) * (p i * p j) + (-2 * R) * (1 : PDE.Mat d) i j)
    ring
  rw [hm, matrixContraction_smul_right, matrixContraction_add_right,
    matrixContraction_smul_right, matrixContraction_smul_right,
    matrixContraction_rankOne, matrixContraction_identity]
  ring

/-- Lower Loewner ellipticity yields the literal native quadratic lower bound. -/
theorem loewner_quadratic_lower  {A : PDE.Mat d} {lam : ℝ}
    (hl : lam • (1 : PDE.Mat d) ≤ A) (p : PDE.Vec d) :
    lam * PDE.vecNormSq p ≤ PDE.vecDot p (A.mulVec p) := by
  have hp := (Matrix.le_iff.mp hl).dotProduct_mulVec_nonneg p
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul] at hp
  aesop

/-- Upper Loewner ellipticity bounds the coefficient trace by `d Lam`. -/
theorem loewner_trace_upper  {A : PDE.Mat d} {Lam : ℝ}
    (hu : A ≤ Lam • (1 : PDE.Mat d)) : A.trace ≤ (d : ℝ) * Lam := by
  have hp := (Matrix.le_iff.mp hu).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at hp
  simp only [Fintype.card_fin, smul_eq_mul] at hp
  linarith

/-- The inverse velocity covariance scalar is nonnegative on the definite strip. -/
theorem gramian_inv_velocity_nonneg {lam h s : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (hs : -(h / 128) ≤ s) : 0 ≤ (gramian lam h s)⁻¹ 1 1 :=
  (posDef_gramian hlam hh hs).inv.posSemidef.diag_nonneg

end HypoellipticAleksandrov.KineticAleksandrov.Holder
