/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorTimeIntegration

/-! The exact Taylor observable follows from the positive square estimate `fundest`. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs


/-- A strict positive gain in [KRV, (fundest)] closes the little-o definition of the Taylor
remainder. -/
theorem twoRooted_littleO_of_majorant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p κ η C r : ℝ)
    (hκ : 1 < κ) (hη : 0 < η) (hC : 0 ≤ C) (hr : 0 < r)
    (hI : ∀ w : ℂ, w ≠ 0 → ‖w‖ ≤ r →
      gammaHalfTwoRootedMajorant P M γ α₁ α₂ α₃ p w ≤
        ENNReal.ofReal (C * ‖w‖ ^ (κ - 2 + η))) :
    IsComplexLittleOAtZero κ (gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃ p) := by
  have twoRooted_term_power_bound (e : ℝ) r (hC : 0 ≤ C) (he : -1 < e) (hr : 0 < r) (hI : ∀ w : ℂ, w ≠ 0 → ‖w‖ ≤ r → gammaHalfTwoRootedMajorant P M γ α₁ α₂ α₃ p w ≤ ENNReal.ofReal (C * ‖w‖ ^ e)) : ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ r → ‖gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃ p z‖ ≤ (4 * ‖p * (p + 1) * (γ ^ 2 / 4) ^ 2‖ * C / (e + 1)) * ‖z‖ ^ (e + 2) := by
    let F₁ : ℂ → ℂ := fun w => ∫ ω,
      ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![w, 0, 1] α₃ ^ (-p - 2)).toReal : ℂ) *
        gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω w ^ 2 ∂P
    let F₂ : ℂ → ℂ := fun w => ∫ ω,
      ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![w, 0, 1] α₃ ^ (-p - 2)).toReal : ℂ) *
        gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω w * gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω w ∂P
    intro z hz hzr
    let c := p * (p + 1) * (γ ^ 2 / 4) ^ 2
    have hP₁ : ‖gammaHalfTwoRootedP1 P M γ α₁ α₂ α₃ p z‖ ≤
        ‖c‖ * ‖z‖ ^ 2 * (C * ‖z‖ ^ e / (e + 1)) := by
      change ‖(c : ℂ) * z ^ 2 * (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) * F₁ ((t : ℂ) * z))‖ ≤ _
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (time_integral_bound F₁ C e r hC he hr (by intro w hw hwr; apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _))).mp; rw [ofReal_norm]; exact (twoRooted_square_expectation_enorm_le P M γ α₁ α₂ α₃ p w).trans (hI w hw hwr)) z hz hzr) (mul_nonneg (norm_nonneg _) (sq_nonneg _))
    have hP₂ : ‖gammaHalfTwoRootedP2 P M γ α₁ α₂ α₃ p z‖ ≤
        2 * ‖c‖ * ‖z‖ ^ 2 * (C * ‖z‖ ^ e / (e + 1)) := by
      unfold gammaHalfTwoRootedP2
      rw [(show 2 * p * (p + 1) * (γ ^ 2 / 4) ^ 2 = 2 * c by dsimp only [c]; ring), norm_mul, norm_mul, norm_mul, norm_star, Complex.norm_real,
        norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      simpa only [F₂, ENNReal.rpow_eq_pow, pow_two, mul_assoc] using (mul_le_mul_of_nonneg_left (time_integral_bound F₂ C e r hC he hr (by intro w hw hwr; apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _))).mp; rw [ofReal_norm]; exact (twoRooted_mixed_expectation_enorm_le P M γ α₁ α₂ α₃ p w).trans (hI w hw hwr)) z hz hzr) (show 0 ≤ (2 * ‖c‖ * ‖z‖) * ‖z‖ by positivity))
    have hP₃ : ‖gammaHalfTwoRootedP3 P M γ α₁ α₂ α₃ p z‖ =
        ‖gammaHalfTwoRootedP1 P M γ α₁ α₂ α₃ p z‖ := norm_star _
    have hsum : ‖gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃ p z‖ ≤
        4 * ‖c‖ * ‖z‖ ^ 2 * (C * ‖z‖ ^ e / (e + 1)) := by
      have hadd := (norm_add_le
        (gammaHalfTwoRootedP1 P M γ α₁ α₂ α₃ p z + gammaHalfTwoRootedP2 P M γ α₁ α₂ α₃ p z)
        (gammaHalfTwoRootedP3 P M γ α₁ α₂ α₃ p z)).trans
          (add_le_add (norm_add_le (gammaHalfTwoRootedP1 P M γ α₁ α₂ α₃ p z)
            (gammaHalfTwoRootedP2 P M γ α₁ α₂ α₃ p z)) le_rfl)
      rw [hP₃] at hadd
      exact hadd.trans (by linarith only [hP₁, hP₂])
    exact hsum.trans_eq (by rw [Real.rpow_add (norm_pos_iff.mpr hz), Real.rpow_two]; ring)
  apply power_bound_littleO _ κ η
    (4 * ‖p * (p + 1) * (γ ^ 2 / 4) ^ 2‖ * C / (κ - 2 + η + 1)) r hη hr
  simpa only [show κ - 2 + η + 2 = κ + η by ring] using (twoRooted_term_power_bound (κ - 2 + η) r hC (by linarith only [hκ, hη]) hr hI)

end DOZZ.Proofs
