module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovarianceBoundsFinal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Physical covariance positivity and scalar evolution equations -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Matrix

variable (lam h s : ℝ)

/-- Position block of the physical polynomial covariance. -/
def covarianceXX  : ℝ :=
  lam * h ^ 3 / 64 + lam * h * s ^ 2 / 64 + lam * s ^ 3 / 3

/-- Mixed block of the physical polynomial covariance. -/
def covarianceXV  : ℝ := lam * h * s / 64 + lam * s ^ 2 / 2

/-- Velocity block of the physical polynomial covariance. -/
def covarianceVV  : ℝ := lam * h / 64 + lam * s

/-- Scalar determinant of the physical polynomial covariance. -/
def covarianceDet  : ℝ :=
  covarianceXX lam h s * covarianceVV lam h s - covarianceXV lam h s ^ 2

/-- Physical scalar blocks agree with the rescaled covariance. -/
theorem gramian_eq_blocks (lam : ℝ) {h : ℝ} (hh : 0 < h) (s : ℝ) :
    gramian lam h s =
      !![covarianceXX lam h s, covarianceXV lam h s;
        covarianceXV lam h s, covarianceVV lam h s] :=
  gramian_eq_polynomial lam hh s

section
variable {lam h s : ℝ} (hlam : 0 < lam) (hh : 0 < h) (hs : -(h / 128) ≤ s)

include hlam hh hs
/-- Positive definiteness of the physical covariance on its actual cutoff domain. -/
theorem posDef_gramian  : (gramian lam h s).PosDef := by
  have hstrip : -(1 / 128 : ℝ) ≤ s / h := by
    apply (le_div_iff₀ hh).mpr
    linarith
  have hD : (covarianceDilation h)ᴴ = covarianceDilation h := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [covarianceDilation, Matrix.conjTranspose]
  have hdet : (covarianceDilation h).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [covarianceDilation, ne_of_gt (Real.rpow_pos_of_pos hh _)]
  have hpos := (posDef_ghat hlam hstrip).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_det_ne_zero hdet)
  simpa only [hD, gramian] using hpos

/-- The physical scalar determinant is strictly positive on the cutoff domain. -/
theorem covarianceDet_pos  : 0 < covarianceDet lam h s := by
  have hp := (posDef_gramian hlam hh hs).det_pos
  rw [gramian_eq_blocks lam hh, Matrix.det_fin_two] at hp
  simpa [covarianceDet, pow_two] using hp
end


/-- Exact inverse covariance, including the off-diagonal symmetry. -/
theorem gramian_inv_blocks (lam : ℝ) {h : ℝ} (hh : 0 < h) (s : ℝ) :
    (gramian lam h s)⁻¹ =
      !![covarianceVV lam h s / covarianceDet lam h s,
        -covarianceXV lam h s / covarianceDet lam h s;
        -covarianceXV lam h s / covarianceDet lam h s,
        covarianceXX lam h s / covarianceDet lam h s] := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, gramian_eq_blocks lam hh]
  rw [Matrix.det_fin_two, Ring.inverse_eq_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [covarianceDet, pow_two, Matrix.smul_apply, div_eq_mul_inv, mul_comm]

variable (lam h s : ℝ)

/-- Position covariance evolves by twice the mixed covariance. -/
theorem hasDerivAt_covarianceXX  :
    HasDerivAt (covarianceXX lam h) (2 * covarianceXV lam h s) s := by
  have hp := ((hasDerivAt_const s (lam * h ^ 3 / 64)).add
    (((hasDerivAt_id s).pow 2).const_mul (lam * h / 64))).add
    (((hasDerivAt_id s).pow 3).const_mul (lam / 3))
  convert hp using 1
  · funext t
    simp only [covarianceXX, Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  · dsimp [covarianceXV]
    ring

/-- Mixed covariance evolves by the velocity covariance. -/
theorem hasDerivAt_covarianceXV  :
    HasDerivAt (covarianceXV lam h) (covarianceVV lam h s) s := by
  have hp := ((hasDerivAt_id s).const_mul (lam * h / 64)).add
    (((hasDerivAt_id s).pow 2).const_mul (lam / 2))
  convert hp using 1
  · funext t
    simp only [covarianceXV, Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  · dsimp [covarianceVV]
    ring

/-- Velocity covariance evolves at the diffusion rate. -/
theorem hasDerivAt_covarianceVV  :
    HasDerivAt (covarianceVV lam h) lam s := by
  convert ((hasDerivAt_id s).const_mul lam).const_add (lam * h / 64) using 1
  · funext t
    dsimp [covarianceVV]
  · simp

/-- Determinant evolution; the transport contributions cancel. -/
theorem hasDerivAt_covarianceDet  :
    HasDerivAt (covarianceDet lam h) (lam * covarianceXX lam h s) s := by
  have hp := ((hasDerivAt_covarianceXX lam h s).mul
    (hasDerivAt_covarianceVV lam h s)).sub ((hasDerivAt_covarianceXV lam h s).pow 2)
  convert hp using 1
  · funext t
    rfl
  · norm_num
    ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
