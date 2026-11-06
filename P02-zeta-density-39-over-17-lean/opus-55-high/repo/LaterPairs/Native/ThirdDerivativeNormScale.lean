module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SecondDerivativeScale
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                            

noncomputable section
namespace TaoTrudgianYang2025

theorem third_derivative_norm_of_square {S N R C : ℝ}
    (hN : 0 ≤ N) (hR : 0 < R) (hC : 1 ≤ C)
    (hb : S^2 ≤ 52*C*N^2/R+384*N*R) :
    S ≤ 20*C*(N/Real.sqrt R+Real.sqrt N*Real.sqrt R) := by
  let u := N/Real.sqrt R
  let v := Real.sqrt N*Real.sqrt R
  pm_61 hu u
  pm_61 hv v
  have hu2 : u^2 = N^2/R := by
    dsimp [u]
    grind
  have hv2 : v^2 = N*R := by
    dsimp [v]
    grind
  have hcu : 52*C ≤ 400*C^2 := by nlinarith
  have hcv : (384:ℝ) ≤ 400*C^2 := by nlinarith
  have hbu := mul_le_mul_of_nonneg_right hcu (sq_nonneg u)
  have hbv := mul_le_mul_of_nonneg_right hcv (sq_nonneg v)
  have hb' : S^2 ≤ 52*C*u^2+384*v^2 := by
    rw [hu2,hv2]
    grind
  have hsq : S^2 ≤ (20*C*(u+v))^2 := by
    have hcuv := mul_nonneg (sq_nonneg C) (mul_nonneg hu hv)
    nlinarith
  have hnonneg : 0 ≤ 20*C*(u+v) := by positivity
  change S ≤ 20*C*(u+v)
  nlinarith

end TaoTrudgianYang2025
