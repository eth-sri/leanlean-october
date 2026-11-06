module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovarianceBoundsScalar
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity



/-! # Uniform covariance estimates with the original ellipticity parameter -/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Matrix
open scoped MatrixOrder

/-- Ellipticity is a scalar factor in the dimensionless covariance. -/
theorem ghat_smul (lam theta : ℝ) : ghat lam theta = lam • ghat 1 theta := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ghat, Matrix.smul_apply] <;> ring

/-- Nonnegative scalar multiplication preserves Loewner order. -/
theorem covariance_smul_le {A B : Matrix (Fin 2) (Fin 2) ℝ} {c : ℝ}
    (h : A ≤ B) (hc : 0 ≤ c) : c • A ≤ c • B := (smul_le_smul_of_nonneg_left h hc)

section
variable {lam theta : ℝ} (hlam : 0 < lam)

include hlam
/-- Upper covariance bound uniform in the ellipticity parameter. -/
theorem ghat_upper  (ht : |theta| ≤ 1) :
    ghat lam theta ≤ (2 * lam) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by

  simpa only [← ghat_smul, smul_smul, mul_comm lam 2] using (covariance_smul_le (ghat_unit_upper ht) hlam.le)

/-- The next-block overlap factor is the source's exact dimensionless factor. -/
theorem ghat_overlap
    (ht0 : -(1 / 128 : ℝ) ≤ theta) (ht1 : theta ≤ 0) :
    ghat lam theta ≤ (13 / 50 : ℝ) • ghat lam (theta + 1) := by
  let sharedTerm_3e542d9605 := ((1 : Matrix (Fin 2) (Fin 2) ℝ))

  have hlower := covariance_smul_le (ghat_unit_next_lower ht0)
    (by norm_num : (0 : ℝ) ≤ 13 / 50)
  have heq : (13 / 50 : ℝ) • ((125 / 2048 : ℝ) •
      sharedTerm_3e542d9605) =
      (65 / 4096 : ℝ) • sharedTerm_3e542d9605 := by
    rw [smul_smul]
    norm_num
  rw [heq] at hlower

  rw [ghat_smul lam theta, ghat_smul lam (theta + 1)]
  simpa only [smul_smul, mul_comm] using (covariance_smul_le ((ghat_unit_cutoff_upper ht0 ht1).trans hlower) hlam.le)
end


/-- Exact velocity diagonal entry of the inverse dimensionless covariance. -/
theorem ghat_inv_velocity (lam theta : ℝ) :
    (ghat lam theta)⁻¹ 1 1 =
      (lam / 64 * (1 + theta ^ 2) + lam * theta ^ 3 / 3) / (ghat lam theta).det := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  simp [ghat, Matrix.smul_apply, div_eq_mul_inv, mul_comm]

/-- Inverse velocity bound, with exactly the source's constant. -/
theorem ghat_inv_velocity_le {lam theta : ℝ} (hlam : 0 < lam)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) : (ghat lam theta)⁻¹ 1 1 ≤ 128 / lam := by


  have hsq : theta ^ 2 ≤ theta := by nlinarith
  have hcube  := pow_nonneg ht0 3
  have hfour  := pow_nonneg ht0 4

  rw [ghat_inv_velocity, div_le_div_iff₀ ((posDef_ghat hlam (show -(1 / 128 : ℝ) ≤ theta by linarith)).det_pos) hlam]
  rw [det_ghat]

  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.Holder
