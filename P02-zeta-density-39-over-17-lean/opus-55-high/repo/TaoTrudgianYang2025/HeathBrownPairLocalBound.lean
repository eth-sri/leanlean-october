module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaUniformityFull
public import TaoTrudgianYang2025.HeathBrownPairSecants
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-! The three actual derivative-error exponents lie below the local secant. -/

noncomputable section

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

section
variable {r : ℝ} (hr : 3 ≤ r)
include r hr
theorem heathBrownPairK_le_derivative :
    heathBrownPairK r ≤ 1/(r*(r-1)) := by
  have h0 : 0 < r := by linarith
  pm_1074 h1 h2
  unfold heathBrownPairK
  pm_23
  have h3 : 0 ≤ r-2 := by linarith
  have h4 : 0 ≤ r+1 := by linarith
  have hp : 0 ≤ (r-1)*(r-2)*(r+1) := by positivity
  grind

theorem heathBrownPairRight_derivative :
    (heathBrownPairRight r-r)/(r*(r-1)) = -1/(r*(r+1)) := by
  have h0 : r ≠ 0 := by linarith
  have h1 : r-1 ≠ 0 := by linarith
  have h2 : r+1 ≠ 0 := by linarith
  unfold heathBrownPairRight
  field_simp
  ring
end

section
variable {r τ : ℝ} (hr : 3 ≤ r)
include r τ hr
theorem heathBrownPairSecant_first_term
    (hτ : τ ≤ heathBrownPairRight r) :
    (τ-r)/(r*(r-1)) ≤ heathBrownPairSecant r τ := by
  have hjoin := heathBrownPairSecant_right hr
  have hright := heathBrownPairRight_derivative hr
  have hs := heathBrownPairK_le_derivative hr
  have hm := mul_nonneg (sub_nonneg.mpr hτ) (sub_nonneg.mpr hs)
  unfold heathBrownPairSecant at hjoin ⊢
  rw [sub_div] at hright ⊢
  simp only [div_eq_mul_inv] at hm hright hjoin ⊢
  grind

theorem heathBrownPairSecant_second_term
    (hτ : heathBrownPairLeft r ≤ τ) :
    -1/(r*(r-1)) ≤ heathBrownPairSecant r τ := by
  have hleft := heathBrownPairSecant_left hr
  have hp := heathBrownPairK_pos hr
  have hm := mul_le_mul_of_nonneg_left hτ hp.le
  unfold heathBrownPairSecant at hleft ⊢
  linarith

theorem heathBrownPairSecant_third_term
    (hτ : heathBrownPairLeft r ≤ τ) :
    -2*τ/(r^2*(r-1)) ≤ heathBrownPairSecant r τ := by
  have h0 : 0 < r := by linarith
  have h1 : 0 < r-1 := by linarith
  have ht : r/2 ≤ τ := (heathBrownPairLeft_half hr).trans hτ
  have heq : -2*(r/2)/(r^2*(r-1)) = -1/(r*(r-1)) := by
    field_simp
  have hle : -2*τ/(r^2*(r-1)) ≤ -1/(r*(r-1)) := by
    rw [← heq]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  exact hle.trans (heathBrownPairSecant_second_term hr hτ)

theorem heathBrownPairSecant_derivative_max
    (hl : heathBrownPairLeft r ≤ τ) (hu : τ ≤ heathBrownPairRight r) :
    max ((τ-r)/(r*(r-1))) (max (-1/(r*(r-1))) (-2*τ/(r^2*(r-1)))) ≤
      heathBrownPairSecant r τ :=
  max_le (heathBrownPairSecant_first_term hr hu)
    (max_le (heathBrownPairSecant_second_term hr hl)
      (heathBrownPairSecant_third_term hr hl))
end

end TaoTrudgianYang2025
