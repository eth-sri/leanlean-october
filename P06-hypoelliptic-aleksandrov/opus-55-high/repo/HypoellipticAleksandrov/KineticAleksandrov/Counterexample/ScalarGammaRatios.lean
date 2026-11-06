module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarPieces
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic

/-!
# Gamma ratios in the negative scalar tail

Euler reflection and recurrence identify the two source trigonometric coefficients.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

private theorem positive_gamma_product_ratio (t u : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) :
    Real.Gamma t * Real.Gamma (1 - t) /
      (Real.Gamma u * Real.Gamma (1 - u)) =
        Real.sin (Real.pi * u) / Real.sin (Real.pi * t) := by
  rw [Real.Gamma_mul_Gamma_one_sub, Real.Gamma_mul_Gamma_one_sub]
  field_simp

variable (gamma : ScalarGamma)

/-- The Gamma ratio in the first negative-ray M term equals Pgamma. -/
theorem gammaA_leading_ratio  :
    gammaA gamma.1 * Real.Gamma (2 / 3) / Real.Gamma (2 / 3 + gamma.1) =
      Pgamma gamma.1 := by
  have hu : 0 < 1 / 3 - gamma.1 := by grind
  have hu1 : 1 / 3 - gamma.1 < 1 := by grind
  have h := positive_gamma_product_ratio (1 / 3) _
    (by norm_num) (by norm_num) hu hu1
  have hs : Real.sin (Real.pi * (1 / 3 - gamma.1)) /
      Real.sin (Real.pi * (1 / 3)) = Pgamma gamma.1 := by
    rw [show Real.pi * (1 / 3 - gamma.1) = Real.pi / 3 - Real.pi * gamma.1 by ring,
      show Real.pi * (1 / 3 : ℝ) = Real.pi / 3 by ring,
      Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three, Pgamma]
    field_simp
  rw [← hs, ← h]
  unfold gammaA
  ring

/-- The Gamma ratio in the signed second M term equals Qgamma. -/
theorem gammaB_leading_ratio  :
    gammaB gamma.1 * Real.Gamma (4 / 3) / Real.Gamma (1 + gamma.1) =
      Qgamma gamma.1 := by
  have hn : -gamma.1 ≠ 0 := neg_ne_zero.mpr gamma.2.1.ne'
  have hgn := Real.Gamma_add_one hn
  have hgp := Real.Gamma_add_one gamma.2.1.ne'
  have h13 := Real.Gamma_add_one (by norm_num : (1 / 3 : ℝ) ≠ 0)
  have hn13 := Real.Gamma_add_one (by norm_num : (-(1 / 3) : ℝ) ≠ 0)
  have h := positive_gamma_product_ratio (1 / 3) gamma.1
    (by norm_num) (by norm_num) gamma.2.1 (by grind)
  norm_num at h13 hn13
  rw [show -gamma.1 + 1 = 1 - gamma.1 by ring] at hgn
  rw [show gamma.1 + 1 = 1 + gamma.1 by ring] at hgp
  have he : gammaB gamma.1 * Real.Gamma (4 / 3) / Real.Gamma (1 + gamma.1) =
      Real.Gamma (1 / 3) * Real.Gamma (2 / 3) /
        (Real.Gamma gamma.1 * Real.Gamma (1 - gamma.1)) := by
    unfold gammaB
    grind
  norm_num only [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at h
  rw [he, h, show Real.pi * (1 / 3 : ℝ) = Real.pi / 3 by ring,
    Real.sin_pi_div_three, Qgamma]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
