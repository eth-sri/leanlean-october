module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.GroupWithZero.Units.Basic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Matrix
open scoped MatrixOrder


/-- Rescaled covariance from the source's transport and velocity diffusion. -/
def ghat (lam theta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![lam / 64 * (1 + theta ^ 2) + lam * theta ^ 3 / 3,
    lam / 64 * theta + lam * theta ^ 2 / 2;
    lam / 64 * theta + lam * theta ^ 2 / 2, lam / 64 + lam * theta]

/-- Kinetic scaling matrix for the covariance. -/
def covarianceDilation (h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![h ^ (3 / 2 : ℝ), 0; 0, h ^ (1 / 2 : ℝ)]

/-- Physical covariance, as the exact rescaling of the dimensionless covariance. -/
def gramian (lam h sigma : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  covarianceDilation h * ghat lam (sigma / h) * covarianceDilation h

/-- Covariance quadratic form in native position–velocity coordinates. -/
def qform {d : ℕ} (lam h sigma : ℝ) (y V : PDE.Vec d) : ℝ :=
  (gramian lam h sigma)⁻¹ 0 0 * PDE.vecDot y y +
    2 * (gramian lam h sigma)⁻¹ 0 1 * PDE.vecDot y V +
    (gramian lam h sigma)⁻¹ 1 1 * PDE.vecDot V V

/-- Velocity component of the inverse covariance applied to the native vector pair. -/
def pform {d : ℕ} (lam h sigma : ℝ) (y V : PDE.Vec d) : PDE.Vec d :=
  (gramian lam h sigma)⁻¹ 1 0 • y + (gramian lam h sigma)⁻¹ 1 1 • V

/-- Determinant of the dimensionless covariance. -/
theorem det_ghat (lam theta : ℝ) :
    (ghat lam theta).det = lam ^ 2 *
      (1 / 4096 + theta / 64 + theta ^ 3 / 192 + theta ^ 4 / 12) := by
  rw [Matrix.det_fin_two]
  simp [ghat]
  ring

/-- Physical covariance agrees with the polynomial Gramian at every real time. -/
theorem gramian_eq_polynomial (lam : ℝ) {h : ℝ} (hh : 0 < h) (sigma : ℝ) :
    gramian lam h sigma =
      !![lam * h ^ 3 / 64 + lam * h * sigma ^ 2 / 64 + lam * sigma ^ 3 / 3,
        lam * h * sigma / 64 + lam * sigma ^ 2 / 2;
        lam * h * sigma / 64 + lam * sigma ^ 2 / 2, lam * h / 64 + lam * sigma] := by
  have hhalf : h ^ (1 / 2 : ℝ) * h ^ (1 / 2 : ℝ) = h := by
    rw [← Real.rpow_add hh]
    norm_num
  have hthree : h ^ (3 / 2 : ℝ) = h * h ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hh, Real.rpow_one]
  have hhalf2 : (h ^ (1 / 2 : ℝ)) ^ 2 = h := by
    simpa only [pow_two] using hhalf
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [gramian, covarianceDilation, ghat, Matrix.mul_apply, Fin.sum_univ_two, hthree]
    ring_nf
    simp only [hhalf2]
  all_goals field_simp [hh.ne']
  all_goals ring



/-- The two-dimensional Sylvester test, stated in literal scalar block coordinates. -/
theorem posDef_two_of_det {a b c : ℝ} (ha : 0 < a) (hdet : 0 < a * b - c ^ 2) :
    (!![a, c; c, b] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]
  · intro x hx
    have hn : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      ext i
      fin_cases i <;> simp [h]
    simp [dotProduct, mulVec, Fin.sum_univ_two]
    have hid : a * (x 0 * (a * x 0 + c * x 1) + x 1 * (c * x 0 + b * x 1)) =
        (a * x 0 + c * x 1) ^ 2 + (a * b - c ^ 2) * (x 1) ^ 2 := by ring
    rcases hn with h0 | h1
    · by_cases h1 : x 1 = 0
      · simp [h1]
        nlinarith [sq_pos_of_ne_zero h0]
      · have hp := mul_pos hdet (sq_pos_of_ne_zero h1)
        nlinarith [sq_nonneg (a * x 0 + c * x 1)]
    · have hp := mul_pos hdet (sq_pos_of_ne_zero h1)
      nlinarith [sq_nonneg (a * x 0 + c * x 1)]

/-- Symmetric diagonal dominance implies positive semidefiniteness in scalar block coordinates. -/
theorem posSemidef_two_of_diagonal {a b c : ℝ} (ha : |c| ≤ a) (hb : |c| ≤ b) :
    (!![a, c; c, b] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]
  · intro x
    simp [dotProduct, mulVec, Fin.sum_univ_two]
    have h0 := mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg (x 0))
    have h1 := mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg (x 1))
    rcases le_total 0 c with hc | hc
    · rw [abs_of_nonneg hc] at h0 h1
      have h2 := mul_nonneg hc (sq_nonneg (x 0 + x 1))
      nlinarith
    · rw [abs_of_nonpos hc] at h0 h1
      have h2 := mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg (x 0 - x 1))
      nlinarith


/-- The dimensionless covariance is positive definite on the entire closed cutoff strip. -/
theorem posDef_ghat {lam theta : ℝ} (hlam : 0 < lam)
    (ht : -(1 / 128 : ℝ) ≤ theta) : (ghat lam theta).PosDef  := by
  have covariance_cube_lower :
      -(1 / 128 : ℝ) ^ 3 ≤ theta ^ 3 := by
    by_cases ht0 : 0 ≤ theta
    · have hp := pow_nonneg ht0 3
      linarith
    · have hneg : 0 ≤ -theta := by linarith
      have hle : -theta ≤ (1 / 128 : ℝ) := by linarith
      have hc := pow_le_pow_left₀ hneg hle 3
      nlinarith
  have hbase : 0 < (1 + theta ^ 2) / 64 + theta ^ 3 / 3 := by
    nlinarith [sq_nonneg theta]
  have hdet : 0 < 1 / 4096 + theta / 64 + theta ^ 3 / 192 + theta ^ 4 / 12 := by
    nlinarith [sq_nonneg (theta ^ 2)]
  unfold ghat
  apply posDef_two_of_det
  · convert mul_pos hlam hbase using 1
    ring
  · have hp := mul_pos (sq_pos_of_pos hlam) hdet
    convert hp using 1
    ring








/-- Ellipticity is a scalar factor in the dimensionless covariance. -/
theorem ghat_smul (lam theta : ℝ) : ghat lam theta = lam • ghat 1 theta := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ghat, Matrix.smul_apply] <;> ring

/-- Nonnegative scalar multiplication preserves Loewner order. -/
theorem covariance_smul_le {A B : Matrix (Fin 2) (Fin 2) ℝ} {c : ℝ}
    (h : A ≤ B) (hc : 0 ≤ c) : c • A ≤ c • B := by
  apply Matrix.le_iff.mpr
  rw [← smul_sub]
  exact (Matrix.le_iff.mp h).smul hc

/-- Upper covariance bound uniform in the ellipticity parameter. -/
theorem ghat_upper {lam theta : ℝ} (hlam : 0 < lam) (ht : |theta| ≤ 1) :
    ghat lam theta ≤ (2 * lam) • (1 : Matrix (Fin 2) (Fin 2) ℝ)  := by
  have ghat_unit_upper :
      ghat 1 theta ≤ (2 : ℝ) • 1 := by
    have ht0 := (abs_le.mp ht).1
    have ht1 := (abs_le.mp ht).2
    have hsq : theta ^ 2 ≤ 1 := by nlinarith
    have hcube : theta ^ 3 ≤ 1 := by
      by_cases h0 : 0 ≤ theta
      · simpa using pow_le_pow_left₀ h0 ht1 3
      · have := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg theta) (not_le.mp h0).le
        nlinarith
    have hc : |theta / 64 + theta ^ 2 / 2| ≤ 33 / 64 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg theta]
    have ha : |-(theta / 64 + theta ^ 2 / 2)| ≤
        2 - ((1 + theta ^ 2) / 64 + theta ^ 3 / 3) := by
      rw [abs_neg]
      linarith
    have hb : |-(theta / 64 + theta ^ 2 / 2)| ≤ 2 - (1 / 64 + theta) := by
      rw [abs_neg]
      linarith
    apply Matrix.le_iff.mpr
    convert posSemidef_two_of_diagonal ha hb using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ghat, Matrix.sub_apply, Matrix.smul_apply]
    all_goals ring
  simpa only [← ghat_smul, smul_smul, mul_comm lam 2] using (covariance_smul_le (ghat_unit_upper) hlam.le)

/-- The next-block overlap factor is the source's exact dimensionless factor. -/
theorem ghat_overlap {lam theta : ℝ} (hlam : 0 < lam)
    (ht0 : -(1 / 128 : ℝ) ≤ theta) (ht1 : theta ≤ 0) :
    ghat lam theta ≤ (13 / 50 : ℝ) • ghat lam (theta + 1)   := by
  have ghat_unit_next_lower :
      (125 / 2048 : ℝ) • 1 ≤ ghat 1 (theta + 1) := by
    let u := theta + 1 / 128
    have hu : 0 ≤ u := by dsimp [u]; linarith
    have ha : 0 < (1 + (theta + 1) ^ 2) / 64 + (theta + 1) ^ 3 / 3 - 125 / 2048 := by
      have heq : (1 + (theta + 1) ^ 2) / 64 + (theta + 1) ^ 3 / 3 - 125 / 2048 =
          u ^ 3 / 3 + 129 * u ^ 2 / 128 + 16637 * u / 16384 + 1859461 / 6291456 := by
        ring
      rw [heq]
      positivity
    have hd : 0 <
        ((1 + (theta + 1) ^ 2) / 64 + (theta + 1) ^ 3 / 3 - 125 / 2048) *
          (1 / 64 + (theta + 1) - 125 / 2048) -
        ((theta + 1) / 64 + (theta + 1) ^ 2 / 2) ^ 2 := by
      have heq :
          ((1 + (theta + 1) ^ 2) / 64 + (theta + 1) ^ 3 / 3 - 125 / 2048) *
            (1 / 64 + (theta + 1) - 125 / 2048) -
          ((theta + 1) / 64 + (theta + 1) ^ 2 / 2) ^ 2 =
          u ^ 4 / 12 + 1939 * u ^ 3 / 6144 + 116971 * u ^ 2 / 262144 +
            23512501 * u / 100663296 + 284017651 / 12884901888 := by dsimp [u]; ring
      rw [heq]
      positivity
    apply Matrix.le_iff.mpr
    convert (posDef_two_of_det ha hd).posSemidef using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ghat, Matrix.sub_apply, Matrix.smul_apply]
    all_goals ring
  have ghat_unit_cutoff_upper :
      ghat 1 theta ≤ (65 / 4096 : ℝ) • 1 := by
    have hsq : theta ^ 2 ≤ (1 / 128 : ℝ) ^ 2 := by nlinarith
    have hcube : theta ^ 3 ≤ 0 := by nlinarith [sq_nonneg theta]
    have hc : |theta / 64 + theta ^ 2 / 2| ≤ (1 / 8192 : ℝ) := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg theta]
    have ha : |-(theta / 64 + theta ^ 2 / 2)| ≤
        65 / 4096 - ((1 + theta ^ 2) / 64 + theta ^ 3 / 3) := by
      rw [abs_neg]
      linarith
    have hb : |-(theta / 64 + theta ^ 2 / 2)| ≤ 65 / 4096 - (1 / 64 + theta) := by
      rw [abs_neg]
      linarith
    apply Matrix.le_iff.mpr
    convert posSemidef_two_of_diagonal ha hb using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ghat, Matrix.sub_apply, Matrix.smul_apply]
    all_goals ring
  have hlower := covariance_smul_le (ghat_unit_next_lower)
    (by norm_num : (0 : ℝ) ≤ 13 / 50)
  have heq : (13 / 50 : ℝ) • ((125 / 2048 : ℝ) •
      1) =
      (65 / 4096 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [smul_smul]
    norm_num
  rw [heq] at hlower
  have h := covariance_smul_le (ghat_unit_cutoff_upper.trans hlower) hlam.le
  rw [ghat_smul lam theta, ghat_smul lam (theta + 1)]
  simpa only [smul_smul, mul_comm] using h

/-- Exact velocity diagonal entry of the inverse dimensionless covariance. -/
theorem ghat_inv_velocity (lam theta : ℝ) :
    (ghat lam theta)⁻¹ 1 1 =
      (lam / 64 * (1 + theta ^ 2) + lam * theta ^ 3 / 3) / (ghat lam theta).det := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  simp [ghat, Matrix.smul_apply, div_eq_mul_inv, mul_comm]

/-- Inverse velocity bound, with exactly the source's constant. -/
theorem ghat_inv_velocity_le {lam theta : ℝ} (hlam : 0 < lam)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) : (ghat lam theta)⁻¹ 1 1 ≤ 128 / lam := by
  have hstrip : -(1 / 128 : ℝ) ≤ theta := by linarith
  have hsq : theta ^ 2 ≤ theta := by nlinarith
  have hscalar : (1 + theta ^ 2) / 64 + theta ^ 3 / 3 ≤
      128 * (1 / 4096 + theta / 64 + theta ^ 3 / 192 + theta ^ 4 / 12) := by
    nlinarith
  rw [ghat_inv_velocity, div_le_div_iff₀ ((posDef_ghat hlam hstrip).det_pos) hlam]
  rw [det_ghat]
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.Holder

