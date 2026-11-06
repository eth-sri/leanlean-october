module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovarianceBoundsTrace
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoff
import Mathlib.Tactic

/-! # Native matrix contractions and ellipticity bounds for the Gaussian sign -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Matrix
open scoped BigOperators MatrixOrder

/- Native rank-one contraction is the corresponding Euclidean quadratic form. -/
theorem matrixContraction_identity {d } (A : PDE.Mat d) :
    matrixContraction A (1 : PDE.Mat d) = A.trace := by
  simp [matrixContraction, Matrix.trace, Matrix.diag, Matrix.one_apply]

/- The exact Gaussian Hessian contraction in native Euclidean coordinates. -/
theorem matrixContraction_gaussian {d } (A : PDE.Mat d) (p : PDE.Vec d) (a R : ℝ) :
    matrixContraction A (fun i j => a * (4 * p i * p j - 2 * R * (1 : PDE.Mat d) i j)) =
      a * (4 * PDE.vecDot p (A.mulVec p) - 2 * R * A.trace) := by
  let K : PDE.Mat d := fun i j => p i * p j
  have hm : (fun i j => a * (4 * p i * p j - 2 * R * (1 : PDE.Mat d) i j)) =
      a • ((4 : ℝ) • K + (-2 * R) • (1 : PDE.Mat d)) := by
    ext i j
    change a * (4 * p i * p j - 2 * R * (1 : PDE.Mat d) i j) =
      a * ((4 : ℝ) * (p i * p j) + (-2 * R) * (1 : PDE.Mat d) i j)
    ring
  have _h_inl_9 (A : PDE.Mat d) (p : PDE.Vec d) : matrixContraction A (fun i j => p i * p j) = PDE.vecDot p (A.mulVec p) := by
    unfold matrixContraction PDE.vecDot Matrix.mulVec dotProduct
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hm, matrixContraction_smul_right, matrixContraction_add_right,
    matrixContraction_smul_right, matrixContraction_smul_right,
    _h_inl_9, matrixContraction_identity]
  ring

/- Lower Loewner ellipticity yields the literal native quadratic lower bound. -/
theorem loewner_quadratic_lower {d } {A : PDE.Mat d} {lam }
    (hl : lam • (1 : PDE.Mat d) ≤ A) (p : PDE.Vec d) :
    lam * PDE.vecNormSq p ≤ PDE.vecDot p (A.mulVec p) := by
  have hp := (Matrix.le_iff.mp hl).dotProduct_mulVec_nonneg p
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hp
  change 0 ≤ PDE.vecDot p (A.mulVec p) - lam * PDE.vecNormSq p at hp
  linarith only [hp]

/- Upper Loewner ellipticity bounds the coefficient trace by `d Lam`. -/
theorem loewner_trace_upper {d } {A : PDE.Mat d} {Lam }
    (hu : A ≤ Lam • (1 : PDE.Mat d)) : A.trace ≤ (d : ℝ) * Lam := by
  have hp := (Matrix.le_iff.mp hu).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at hp
  simp only [Fintype.card_fin, smul_eq_mul] at hp
  linarith only [hp]

/- The inverse velocity covariance scalar is nonnegative on the definite strip. -/
theorem gramian_inv_velocity_nonneg {lam h s } (hlam : 0 < lam) (hh : 0 < h)
    (hs : -(h / 128) ≤ s) : 0 ≤ (gramian lam h s)⁻¹ 1 1 :=
  (posDef_gramian hlam hh hs).inv.posSemidef.diag_nonneg

end HypoellipticAleksandrov.KineticAleksandrov.Holder
