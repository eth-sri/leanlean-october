module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureTimeDerivative
import Mathlib.Tactic

/-! # A uniform integrable derivative majorant away from the Gaussian pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Time decomposition of the Gaussian derivative bound, for a squared-distance lower bound a. -/
def bellmanDerivativeMajorant (a : ℝ) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator
    (fun _ => 360 * 8 ^ 6 * Real.sqrt 3 / (Real.pi * a ^ 6)) t +
  (Ioi (1 : ℝ)).indicator (fun s => Real.sqrt 3 / (2 * Real.pi) * s ^ (-2 : ℝ)) t

/-- The derivative majorant is integrable on the positive half-line. -/
theorem integrable_bellmanDerivativeMajorant (a : ℝ) :
    Integrable (fun t : BellmanPositiveTime => bellmanDerivativeMajorant a t.val)
      bellmanPositiveTimeVolume := integrable_bellmanPositiveTime_majorant _

/-- The actual Gaussian time derivative has an integrable separated bound. -/
theorem bellmanGaussianTimeDerivative_le_majorant (a : ℝ) (ha : 0 < a)
    (q : ℝ × ℝ) (hq : a ≤ q.1 ^ 2 + q.2 ^ 2) (t : BellmanPositiveTime) :
    ‖bellmanGaussianTimeCoefficient t.val q * bellmanGaussianKernel t q‖ ≤
      bellmanGaussianTimeWeight q * bellmanDerivativeMajorant a t.val := by
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (bellmanGaussianKernel_pos t q)]
  by_cases ht : t.val ≤ 1
  · simp only [bellmanDerivativeMajorant, indicator_of_mem
      (show t.val ∈ Ioc (0 : ℝ) 1 from ⟨t.property, ht⟩),
      indicator_of_notMem (show t.val ∉ Ioi (1 : ℝ) from not_lt.mpr ht), add_zero]
    have h := mul_le_mul (bellmanGaussianTimeCoefficient_small t ht q)
      (bellmanGaussianKernel_le_smallTime_four t ht q a ha hq)
      (bellmanGaussianKernel_pos t q).le
      (div_nonneg (bellmanGaussianTimeWeight_nonneg q) (by positivity))
    refine h.trans_eq ?_
    field_simp [ne_of_gt t.property]
  · have h1 := lt_of_not_ge ht
    simp only [bellmanDerivativeMajorant, indicator_of_notMem
      (show t.val ∉ Ioc (0 : ℝ) 1 from fun h => ht h.2),
      indicator_of_mem (show t.val ∈ Ioi (1 : ℝ) from h1), zero_add]
    have h := mul_le_mul (bellmanGaussianTimeCoefficient_large t h1.le q)
      (bellmanGaussianKernel_le t q) (bellmanGaussianKernel_pos t q).le
      (bellmanGaussianTimeWeight_nonneg q)
    refine h.trans_eq ?_
    rw [Real.rpow_neg t.property.le, Real.rpow_two]
    ring

end HypoellipticAleksandrov.KineticAleksandrov
