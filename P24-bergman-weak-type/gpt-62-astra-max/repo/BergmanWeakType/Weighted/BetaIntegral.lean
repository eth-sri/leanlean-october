/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions
public import BergmanWeakType.Calculus
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Real beta integrals for the weighted boundary constants -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace BergmanWeakType

theorem integral_real_beta {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  calc
    _ = Complex.betaIntegral a b := by
      apply intervalIntegral.integral_congr_Ioo_of_le (zero_le_one)
      intro x hx
      simp [Complex.ofReal_cpow hx.1.le, Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le)]
    _ = _ := by
      rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by assumption) (by assumption)]
      rw [← Complex.ofReal_add]
      simp only [Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]

open Real in
/-- The symmetric beta substitution `t = (1-cos x)/2` covers the full
semicircle at once. Legendre duplication then gives the sharp constant. -/
theorem scaled_integral_sin {α : ℝ} (hα : -1 < α) :
    2^α * (∫ x in 0..π, sin x ^ α) = π * gammaConstant α := by
  let a := (α+1)/2
  have ha : 0 < a := by grind
  let t x := (1-cos x)/2
  let g (u : ℝ) := u^(a-1)*(1-u)^(a-1)
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := 0) (b := π)
    (g := g) (f := t) (f' := fun x ↦ sin x/2) (by fun_prop)
    (fun x _ ↦ by unfold t; scalar_deriv [hasDerivAt_cos]; ring)
    (fun x hx ↦ by simp [pi_pos.le] at hx; exact (half_pos (sin_pos_of_pos_of_lt_pi hx.1 hx.2)).le)
  have ht (x : ℝ) : 0 ≤ t x := by dsimp [t]; linarith [cos_le_one x]
  have hc (x : ℝ) : 0 ≤ 1-t x := by dsimp [t]; linarith [neg_one_le_cos x]
  have hg : (∫ x in 0..π, sin x ^ α) / 2^α = Gamma a ^ 2 / Gamma (α+1) := by
    rw [← intervalIntegral.integral_div]
    calc
      _ = ∫ x in 0..π, (g ∘ t) x * (sin x/2) := by
        apply intervalIntegral.integral_congr_Ioo_of_le pi_pos.le
        intro x hx
        have hs := sin_pos_of_pos_of_lt_pi hx.1 hx.2
        have he : t x * (1-t x) = (sin x/2)^2 := by dsimp [t]; nlinarith [sin_sq_add_cos_sq x]
        dsimp [g]; rw [← mul_rpow (ht x) (hc x), he, ← rpow_natCast_mul (half_pos hs).le 2, Nat.cast_ofNat,
          show 2*(a-1) = α-1 by ring, rpow_sub_one (half_pos hs).ne',
          div_mul_cancel₀ _ (half_pos hs).ne', div_rpow hs.le zero_le_two]
      _ = _ := by
        rw [h]; simpa [t, sq, show a+a = α+1 by ring] using integral_real_beta ha ha
  have hd := Gamma_mul_Gamma_add_half_of_pos ha
  rw [show 2*a = α+1 by ring, show 1-(α+1) = -α by ring, rpow_neg zero_le_two] at hd
  have hG : Gamma (1+α/2) ≠ 0 := (Gamma_pos_of_pos (by linarith)).ne'
  have htwo : (2:ℝ)^α ≠ 0 := by positivity
  unfold gammaConstant
  grind [sq_sqrt pi_pos.le]

end BergmanWeakType
