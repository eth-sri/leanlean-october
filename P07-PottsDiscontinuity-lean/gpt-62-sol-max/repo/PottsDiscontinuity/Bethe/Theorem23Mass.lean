module

public import PottsDiscontinuity.Bethe.Prop21Rho

/-! # Exact physical masses of the discrete and continuous densities -/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem integral_Rsech {lam : ℝ} (hlam : 0 < lam) :
    (∫ α in (-Real.pi)..Real.pi, Rsech lam α) = Real.pi := by
  have heq :=
    funext (Rsech_eq_trigSeries hlam)
  grind [cosCoeff_zero, cosCoeff_trigSeries_zero, summable_secCoeff, summable_zero]

theorem integral_rho_mass {Δ : ℝ} (hΔ : Δ < -1) :
    (∫ x in (-Real.pi)..Real.pi, rho Δ x) = 1 / 2 := by
  have hlam := lamOf_pos hΔ
  rw [integral_Icc_comp_kMap hlam]
  have heq : (fun α => Xi (lamOf Δ) α * rho Δ (kMap (lamOf Δ) α)) =
      fun α => (2 * Real.pi)⁻¹ * Rsech (lamOf Δ) α := by
    funext α
    have h := Rtrans_rho hΔ α
    rw [Rtrans_eq hΔ] at h
    field_simp
    linarith
  rw [heq, intervalIntegral.integral_const_mul, integral_Rsech hlam]
  field_simp

end PottsDiscontinuity.Bethe
