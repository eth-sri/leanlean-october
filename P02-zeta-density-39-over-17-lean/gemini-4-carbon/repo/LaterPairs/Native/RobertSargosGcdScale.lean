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
public import LaterPairs.Native.RobertSargosGcdFiberCount

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                               

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_gcd_scale_bound {R H Q δ η j k : ℝ}
    (hR : 1 ≤ R) (hH : 1 ≤ H) (hQ : 1 ≤ Q)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hj : 1 ≤ j) (hk : 1 ≤ k) (hkQ : k ≤ 2*Q) :
    ((R/j)*(H/j)*(max 1 (Q/k)))^(1+η)*(1+δ*max 1 (Q/k)) ≤
      4*(2:ℝ)^η*(R*H*Q)^(1+η)*(1+δ*Q)/(j*k) := by
  have hRp : 0 < R := by linarith
  have hHp : 0 < H := by linarith
  have hQp : 0 < Q := by linarith
  have hjp : 0 < j := by linarith
  have hkp : 0 < k := by linarith
  have hBp : 0 < R*H*Q := by positivity
  have hnp : 0 < (R/j)*(H/j)*(max 1 (Q/k)) := by positivity
  have hq : max 1 (Q/k) ≤ 2*Q/k := by
    apply max_le
    · exact (le_div_iff₀ hkp).mpr (by simpa using hkQ)
    · exact div_le_div_of_nonneg_right (by linarith) hkp.le
  have hq2 := hq.trans (div_le_self (by positivity) hk)
  have hlin : (R/j)*(H/j)*(max 1 (Q/k)) ≤ 2*(R*H*Q)/(j*k) := by
    exact (mul_le_mul
          (mul_le_mul_of_nonneg_right (div_le_self hRp.le hj) (by positivity))
          hq (by positivity) (by positivity)).trans_eq (by field_simp)
  have hlast : 1+δ*max 1 (Q/k) ≤ 2*(1+δ*Q) := by
    nlinarith
  calc
    _ = ((R/j)*(H/j)*(max 1 (Q/k)))*
        ((R/j)*(H/j)*(max 1 (Q/k)))^η*(1+δ*max 1 (Q/k)) := by
      rw [Real.rpow_add hnp,Real.rpow_one]
    _ ≤ (2*(R*H*Q)/(j*k))*(2*(R*H*Q))^η*(2*(1+δ*Q)) :=
      mul_le_mul (mul_le_mul hlin (Real.rpow_le_rpow hnp.le (hlin.trans (div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le hj hk))) hη) (by positivity) (by positivity))
        hlast (by positivity) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hBp.le,
        Real.rpow_add hBp,Real.rpow_one]
      ring

end TaoTrudgianYang2025

