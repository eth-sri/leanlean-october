module

public import PottsDiscontinuity.BetheAnsatz.Defs

/-!
# Scalar scattering identities for the coordinate Bethe Ansatz

Companion paper arXiv:1611.09909v1, Lemma `lem:ratios`, equation (6), and equation (19).
The positivity of the real part of `S` makes all scattering factors nonzero for `Δ < -1`.
The Bethe equations and distinctness of the roots are not needed for these identities.
-/

@[expose] public section

open Complex

namespace PottsDiscontinuity.BetheAnsatz

open Bethe

theorem scattering_re (Δ x y : ℝ) :
    (scattering Δ x y).re = Real.cos x + Real.cos y - 2 * Δ := by
  rw [scattering, z, exp_neg_I_mul_ofReal, exp_I_mul_ofReal]
  aesop

theorem scattering_re_pos {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    0 < (scattering Δ x y).re := by
  rw [scattering_re]
  exact cos_add_cos_sub_pos hΔ x y

theorem scattering_ne_zero {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    scattering Δ x y ≠ 0 := by
  intro h
  have := scattering_re_pos hΔ x y
  simp_all

/-- On the momentum interval used in Theorem 3.1, only the zero root gives `z = 1`. -/
theorem z_ne_one {p : ℝ} (hp : p ∈ Set.Ioo (-Real.pi) Real.pi) (hp0 : p ≠ 0) :
    z p ≠ 1 := by
  intro h
  have h' : Complex.exp (I * (p : ℂ)) = Complex.exp 0 := by aesop
  have heq := (Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by simpa using hp.1) (by simpa using hp.2.le)
    (by simpa using (neg_lt_zero.mpr Real.pi_pos)) (by simpa using Real.pi_pos.le)) h'
  simp_all

theorem scattering_eq_inv_z (Δ x y : ℝ) :
    scattering Δ x y = (z x)⁻¹ + z y - 2 * (Δ : ℂ) := by
  rw [scattering, Complex.exp_neg]
  rfl

theorem z_mul_scattering (Δ x y : ℝ) :
    z x * scattering Δ x y = 1 + z x * z y - 2 * (Δ : ℂ) * z x := by
  rw [scattering_eq_inv_z, mul_sub, mul_add, mul_inv_cancel₀ (z_ne_zero x)]
  ring

/-- The positive-exponent version of the phase identity defining `Θ`. -/
theorem exp_I_theta_eq_scattering {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    Complex.exp (I * (theta Δ x y : ℂ)) =
      z y * scattering Δ y x / (z x * scattering Δ x y) := by
  have h := exp_neg_I_theta hΔ y x
  rw [theta_swap, Complex.ofReal_neg, mul_neg, neg_neg] at h
  rw [h, thetaRhs, mul_sub, Complex.exp_sub]
  grind only [z, scattering]

/-- Cancellation of the two simple poles. -/
theorem L_add_M (c : ℝ) {w : ℂ} (hw : w ≠ 1) :
    L c w + M c w = 2 - (c : ℂ) ^ 2 := by
  have hd : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  unfold L M
  field_simp
  ring

theorem M_eq_neg_scattering_zero (c : ℝ) {y : ℝ} (hy : z y ≠ 1) :
    M c (z y) = -scattering (anisotropy c) 0 y / (1 - z y) := by
  rw [scattering_eq_inv_z, z_zero, inv_one]
  have hy1 := sub_ne_zero.mpr hy.symm
  unfold M anisotropy
  push_cast
  field_simp
  ring

theorem M_ne_zero {c y : ℝ} (hc : 2 < c) (hy : z y ≠ 1) : M c (z y) ≠ 0 := by
  rw [M_eq_neg_scattering_zero c hy]
  exact div_ne_zero (neg_ne_zero.mpr (scattering_ne_zero (anisotropy_lt_neg_one hc) 0 y))
    (sub_ne_zero.mpr hy.symm)

end PottsDiscontinuity.BetheAnsatz
