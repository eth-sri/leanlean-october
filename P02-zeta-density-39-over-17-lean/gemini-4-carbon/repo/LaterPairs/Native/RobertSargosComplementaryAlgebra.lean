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
public import LaterPairs.Native.RobertSargosComplementaryCount

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                               

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_conic_count_algebra {R H Q δ : ℝ}
    (hR : 1 ≤ R) (hH : 1 ≤ H) (hQ : 1 ≤ Q)
    (hδ : 0 ≤ δ) (hQH : Q ≤ H) (hδR : δ ≤ R/H) :
    Q*(1+(δ*Q+99*R*Q/H))*(Q+8*H^2*δ) ≤
      1000*(R*H*Q)*(1+δ*Q) := by
  have hHp : 0 < H := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hRH := le_mul_of_one_le_left hHp.le hR
  have hq := hQH.trans hRH
  have h1 : Q^2 ≤ R*H*Q := by nlinarith
  have hsq := pow_le_pow_left₀ hQ0 hQH 2
  have h2 : R*Q^3/H ≤ R*H*Q := by
    apply (div_le_iff₀ hHp).mpr
    nlinarith
  have h3 : 8*δ*H^2*Q ≤ 8*(R*H*Q) := by
    have hδH := (le_div_iff₀ hHp).mp hδR
    nlinarith
  have hb : 1+(δ*Q+99*R*Q/H) ≤ 100*(1+R*Q/H) := by
    have hm := mul_le_mul_of_nonneg_right hδR hQ0
    have he : (R/H)*Q = R*Q/H := by ring
    rw [he] at hm
    rw [show 99*R*Q/H = 99*(R*Q/H) from by ring]
    linarith
  have hid : Q*(1+R*Q/H)*(Q+8*H^2*δ) =
      Q^2+R*Q^3/H+8*δ*H^2*Q+8*δ*R*H*Q^2 := by
    field_simp
    ring
  have hsmall : Q*(1+R*Q/H)*(Q+8*H^2*δ) ≤
      10*(R*H*Q)*(1+δ*Q) := by
    rw [hid]
    have hpos : 0 ≤ δ*R*H*Q^2 := by positivity
    nlinarith
  calc
    _ ≤ Q*(100*(1+R*Q/H))*(Q+8*H^2*δ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hQ0) (by positivity)
    _ = 100*(Q*(1+R*Q/H)*(Q+8*H^2*δ)) := by ring
    _ ≤ 100*(10*(R*H*Q)*(1+δ*Q)) :=
      mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ = _ := by ring

theorem robertSargos_linear_count_algebra {R H Q δ : ℝ}
    (hR : 1 ≤ R) (hH : 1 ≤ H) (hQ : 1 ≤ Q)
    (hδ : 0 ≤ δ) (hQH : Q ≤ H) (hRδ : R/H ≤ δ) :
    Q*(1+(δ*Q+99*R*Q/H))*(Q+72*H*R) ≤
      7300*(R*H*Q)*(1+δ*Q) := by
  have hHp : 0 < H := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hb : 1+(δ*Q+99*R*Q/H) ≤ 100*(1+δ*Q) := by
    have hm := mul_le_mul_of_nonneg_right hRδ hQ0
    have he : (R/H)*Q = R*Q/H := by ring
    rw [he] at hm
    rw [show 99*R*Q/H = 99*(R*Q/H) from by ring]
    linarith
  have hl : Q+72*H*R ≤ 73*R*H := by nlinarith
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hb hQ0) hl
        (by positivity) (by positivity)).trans_eq (by ring)

theorem robertSargos_frequency_loss_algebra {R H Q δ ε K W : ℝ}
    (hR : 1 ≤ R) (hH : 1 ≤ H) (hQ : 1 ≤ Q)
    (hε : 0 ≤ ε) (hW : 0 ≤ W)
    (hbound : W ≤ K*(R*H*Q)*(1+δ*Q)) :
    Q^ε*W ≤ K*(R*H*Q)^(1+ε)*(1+δ*Q) := by
  have hQ0 : 0 ≤ Q := by linarith
  have hB : 0 < R*H*Q := by positivity
  have hQB : Q ≤ R*H*Q := by
    have hRH := one_le_mul_of_one_le_of_one_le hR hH
    nlinarith
  exact (mul_le_mul (Real.rpow_le_rpow hQ0 hQB hε) hbound hW (by positivity)).trans_eq (by rw [Real.rpow_add hB,Real.rpow_one]; ring)

end TaoTrudgianYang2025
