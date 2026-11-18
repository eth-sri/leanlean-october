module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import MathCollab.Density.Stronger.Atkinson.FiniteWeightVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCutoffVariation
public import MathCollab.Density.Stronger.Atkinson.ZetaBandSecondDerivatives
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFirstDerivative
public import MathCollab.Density.Stronger.Atkinson.FresnelEvaluation
public import MathCollab.Density.Stronger.Atkinson.ContinuousKernelPrimitive
public import MathCollab.Density.Stronger.Atkinson.IntervalSecondDerivativeBounds
public import MathCollab.Density.Stronger.Atkinson.SecondDerivativeComposition
public import MathCollab.Density.Stronger.PointMean.HorizontalEdges
public import MathCollab.Density.Stronger.Fourth.SquareTail
public import LaterPairs.Native.RobertSargosDisplacement

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                 

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_ratio_square_gap {r q₁ q₂ h₁ h₂ d H Q δ : ℝ}
    (hH : 0 < H) (hQ : 0 < Q) (hδ : 0 ≤ δ)
    (hr : |r| ≤ H/2) (hh₂ : H ≤ h₂) (hq₁ : Q ≤ |q₁|)
    (hlin : r*d+h₁*q₁-h₂*q₂ = 0)
    (hnear : |robertSargosReduced r q₁ q₂ h₁ h₂ d| ≤ δ*H*Q^2) :
    |(q₂/q₁)^2-h₁*(h₁-r)/(h₂*(h₂-r))| ≤ 2*δ*|r|/H := by
  have hhp := hH.trans_le hh₂
  have hdiff : H/2 ≤ h₂-r := by linarith [le_abs_self r]
  have hdiffp : 0 < h₂-r := by linarith
  have hqp := hQ.trans_le hq₁
  have hqn := abs_pos.mp hqp
  have ha := mul_pos hhp hdiffp
  have haLower : H^2/2 ≤ h₂*(h₂-r) := by
    have hm := mul_le_mul hh₂ hdiff (by positivity : 0 ≤ H/2) hhp.le
    nlinarith
  have hqLower : Q^2 ≤ q₁^2 := by
    have hm := sq_le_sq₀ hQ.le (abs_nonneg q₁) |>.mpr hq₁
    simpa using hm
  have hden := mul_pos ha (sq_pos_of_ne_zero hqn)
  have hdenLower := mul_le_mul haLower hqLower (sq_nonneg Q) ha.le
  have he : (q₂/q₁)^2-h₁*(h₁-r)/(h₂*(h₂-r)) =
      r*robertSargosReduced r q₁ q₂ h₁ h₂ d/((h₂*(h₂-r))*q₁^2) := by
    rw [robertSargos_reduced_factor hlin]
    field_simp
  rw [he,abs_div,abs_mul,abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  calc
    |r| * |robertSargosReduced r q₁ q₂ h₁ h₂ d| ≤ |r| * (δ*H*Q^2) :=
      mul_le_mul_of_nonneg_left hnear (abs_nonneg r)
    _ = (2*δ*|r|/H)*((H^2/2)*Q^2) := by field_simp
    _ ≤ (2*δ*|r|/H)*((h₂*(h₂-r))*q₁^2) :=
      mul_le_mul_of_nonneg_left hdenLower (by positivity)

                                                                      
                                                                         
theorem robertSargos_ratio_sqrt_gap {r q₁ q₂ h₁ h₂ d H Q δ : ℝ}
    (hH : 0 < H) (hQ : 0 < Q) (hδ : 0 ≤ δ)
    (hr : |r| ≤ H/2) (hh₁ : H ≤ h₁) (hh₂ : H ≤ h₂)
    (hq₁ : |q₁| ∈ Set.Icc Q (2*Q)) (hq₂ : Q ≤ |q₂|)
    (hsign : 0 < q₁*q₂)
    (hlin : r*d+h₁*q₁-h₂*q₂ = 0)
    (hnear : |robertSargosReduced r q₁ q₂ h₁ h₂ d| ≤ δ*H*Q^2) :
    |q₂/q₁-Real.sqrt (h₁*(h₁-r)/(h₂*(h₂-r)))| ≤ 4*δ*|r|/H := by
  have hratio : 0 < q₂/q₁ := by
    rcases mul_pos_iff.mp hsign with hp | hn
    · exact div_pos hp.2 hp.1
    · exact div_pos_of_neg_of_neg hn.2 hn.1
  have hhalf : 1/2 ≤ q₂/q₁ := by
    rw [← abs_of_pos hratio,abs_div]
    apply (le_div_iff₀ (hQ.trans_le hq₁.1)).mpr
    linarith [hq₁.2]
  have hA : 0 ≤ h₁*(h₁-r)/(h₂*(h₂-r)) := by
    have hrle := (le_abs_self r).trans hr
    exact div_nonneg (mul_nonneg (by linarith) (by linarith))
      (mul_nonneg (by linarith) (by linarith))
  have hs := robertSargos_ratio_square_gap hH hQ hδ hr hh₂ hq₁.1 hlin hnear
  let A := h₁*(h₁-r)/(h₂*(h₂-r))
  have hsq := Real.sq_sqrt hA
  have hroot := Real.sqrt_nonneg A
  have hid : |(q₂/q₁)^2-A| = |q₂/q₁-Real.sqrt A| * (q₂/q₁+Real.sqrt A) := by
    rw [show (q₂/q₁)^2-A = (q₂/q₁-Real.sqrt A)*(q₂/q₁+Real.sqrt A) by nlinarith,
      abs_mul,abs_of_nonneg (by positivity : 0 ≤ q₂/q₁+Real.sqrt A)]
  change |(q₂/q₁)^2-A| ≤ 2*δ*|r|/H at hs
  rw [hid] at hs
  change |q₂/q₁-Real.sqrt A| ≤ 4*δ*|r|/H
  have hm := mul_le_mul_of_nonneg_left (show 1/2 ≤ q₂/q₁+Real.sqrt A by linarith)
    (abs_nonneg (q₂/q₁-Real.sqrt A))
  convert (mul_le_mul_of_nonneg_left (hm.trans hs) (by norm_num : (0:ℝ) ≤ 2)) using 1 <;> ring

end TaoTrudgianYang2025
