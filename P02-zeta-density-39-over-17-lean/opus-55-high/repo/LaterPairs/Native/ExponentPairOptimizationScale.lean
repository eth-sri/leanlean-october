module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.ExponentPairDifferencingBound
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                           

noncomputable section

namespace TaoTrudgianYang2025

def aProcessOptimizationScale (q p T N : ℝ) : ℝ :=
  (T/N)^(-q/(q+1))*N^((1-p+q)/(q+1))

section
variable {q p T N : ℝ}
include q p T N
theorem aProcessOptimizationScale_pos
    (hT : 0 < T) (hN : 0 < N) :
    0 < aProcessOptimizationScale q p T N := by
  unfold aProcessOptimizationScale
  positivity

theorem aProcessOptimizationScale_le
    (hq : 0 ≤ q) (hp : 0 ≤ p) (hN : 1 ≤ N) (hNT : N ≤ T) :
    aProcessOptimizationScale q p T N ≤ N := by
  have hNpos := zero_lt_one.trans_le hN
  pm_6237
  have hden : 0 < q+1 := by linarith
  have h₁ : (T/N)^(-q/(q+1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hratio (div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le)
  have h₂ : N^((1-p+q)/(q+1)) ≤ N := by
    calc
      _ ≤ N^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN
        ((div_le_iff₀ hden).mpr (by linarith))
      _ = N := Real.rpow_one _
  unfold aProcessOptimizationScale
  have hp₂ : 0 ≤ N^((1-p+q)/(q+1)) := by positivity
  exact (mul_le_mul_of_nonneg_right h₁ hp₂).trans (by grind)

theorem aProcessOptimizationScale_log
    (hT : 0 < T) (hN : 0 < N) :
    Real.log (aProcessOptimizationScale q p T N) =
      (-q/(q+1))*Real.log (T/N)+((1-p+q)/(q+1))*Real.log N := by
  have hratio : 0 < T/N := by positivity
  rw [aProcessOptimizationScale,Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hratio,Real.log_rpow hN]
end

section
variable {q p T N : ℝ} (hq : 0 ≤ q) (hT : 0 < T) (hN : 0 < N)
include q p T N hq hT hN
theorem aProcessOptimizationScale_balance :
    ((T/N^2)^q*N^p)*(aProcessOptimizationScale q p T N)^(q+1) = N := by
  pm_2550
  have hM : 0 < (T/N^2)^q*N^p := by positivity
  apply Real.log_injOn_pos (mul_pos hM (Real.rpow_pos_of_pos hR _)) hN
  rw [Real.log_mul hM.ne' (Real.rpow_pos_of_pos hR _).ne',
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity),Real.log_rpow hN,Real.log_rpow hR,
    aProcessOptimizationScale_log hT hN]
  rw [show T/N^2 = (T/N)/N by ring,Real.log_div hratio.ne' hN.ne']
  field_simp
  ring

theorem aProcessOptimizationScale_cost :
    N^2/aProcessOptimizationScale q p T N =
      (T/N)^(q/(q+1))*N^(1+p/(q+1)) := by
  pm_2550
  apply Real.log_injOn_pos (div_pos (sq_pos_of_pos hN) hR)
    (show 0 < (T/N)^(q/(q+1))*N^(1+p/(q+1)) by positivity)
  rw [Real.log_div (by positivity) hR.ne',Real.log_pow,
    aProcessOptimizationScale_log hT hN,
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hratio,Real.log_rpow hN]
  field_simp
  ring
end

end TaoTrudgianYang2025
