module

public import DedekindZetaZeroFree.Analysis.Gamma.ReciprocalRecurrenceAndRisingProducts
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.DerivativeIntegrationByParts

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def originMellinChart (h : ℝ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) *
    mellin (iteratedDeriv n h) (s + (n : ℂ)) *
    (Complex.Gammaℂ (s + (n : ℂ)))⁻¹

variable (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (n : ℕ) (s : ℂ)
    (hs : -(n : ℝ) < s.re)

include hh hc hs in
theorem originMellinChart_differentiableAt :
    DifferentiableAt ℂ (originMellinChart h n) s := by
  rw [show originMellinChart h n = (fun z : ℂ =>
      ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) *
        mellin (iteratedDeriv n h) (z + (n : ℂ)) *
        (Complex.Gammaℂ (z + (n : ℂ)))⁻¹) from rfl]
  exact ((differentiableAt_const ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n)).mul ((differentiableAt_comp_add_const
     ).2
    (differentiableAt_mellin_iteratedDeriv_of_pos hh hc n (by
      rw [show (s + (n : ℂ)).re = s.re + (n : ℝ) by simp [Complex.add_re]]
      linarith)))).mul ((differentiableAt_comp_add_const
     ).2
    (Complex.differentiable_Gammaℂ_inv.differentiableAt))

include hh hc hs in
theorem originMellinChart_succ :
    originMellinChart h (n + 1) s = originMellinChart h n s := by
  have hcast : s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 := by push_cast; ring
  let mellin₀ := mellin (iteratedDeriv n h) (s + (n : ℂ))
  have hA : originMellinChart h (n + 1) s =
      ((-1 : ℂ) ^ (n + 1) / (2 * (Real.pi : ℂ)) ^ (n + 1)) *
        (-(s + (n : ℂ)) * mellin₀) *
        (Complex.Gammaℂ ((s + (n : ℂ)) + 1))⁻¹ := by
    simp only [originMellinChart, hcast, iteratedDeriv_succ]
    rw [mellin_deriv_eq_neg_mul (iteratedDeriv n h) (contDiff_iteratedDeriv h hh n) (hasCompactSupport_iteratedDeriv h hc n) (s + (n : ℂ)) (by
      rw [show (s + (n : ℂ)).re = s.re + (n : ℝ) by simp [Complex.add_re]]
      linarith)]
  have hCn : ((-1 : ℂ) ^ (n + 1) / (2 * (Real.pi : ℂ)) ^ (n + 1)) * (-(s + (n : ℂ)))
      = ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) *
          ((s + (n : ℂ)) / (2 * (Real.pi : ℂ))) := by
    rw [pow_succ, pow_succ]
    field_simp
  rw [hA, show originMellinChart h n s =
      ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) *
        mellin₀ *
        (Complex.Gammaℂ (s + (n : ℂ)))⁻¹ from rfl,
    inverse_Gammaℂ_recurrence (s + (n : ℂ))]
  exact calc
    ((-1 : ℂ) ^ (n + 1) / (2 * (Real.pi : ℂ)) ^ (n + 1)) *
        (-(s + (n : ℂ)) * mellin₀) *
        (Complex.Gammaℂ ((s + (n : ℂ)) + 1))⁻¹
      = (((-1 : ℂ) ^ (n + 1) / (2 * (Real.pi : ℂ)) ^ (n + 1)) * (-(s + (n : ℂ)))) *
          (mellin₀ *
            (Complex.Gammaℂ ((s + (n : ℂ)) + 1))⁻¹) := by ring
    _ = (((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) *
            ((s + (n : ℂ)) / (2 * (Real.pi : ℂ)))) *
          (mellin₀ *
            (Complex.Gammaℂ ((s + (n : ℂ)) + 1))⁻¹) := by rw [hCn]
    _ = ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) *
          mellin₀ *
          (((s + (n : ℂ)) / (2 * (Real.pi : ℂ))) *
            (Complex.Gammaℂ ((s + (n : ℂ)) + 1))⁻¹) := by ring

end DedekindZetaZeroFree.LargeSieve.Vendor

end
