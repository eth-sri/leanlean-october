module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureMajorant
import Mathlib.Tactic

/-! # Integrable bounds for the time derivative away from the Gaussian pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/- The scalar time chart of the literal positive-time Gaussian. -/
def bellmanGaussianTimeChart (s : ℝ) (q : ℝ × ℝ) : ℝ :=
  Real.sqrt 3 / (2 * Real.pi * s ^ 2) *
    Real.exp (-3 * q.1 ^ 2 / s ^ 3 + 3 * q.1 * q.2 / s ^ 2 - q.2 ^ 2 / s)

/- The coefficient of the Gaussian in its time derivative. -/
def bellmanGaussianTimeCoefficient (s : ℝ) (q : ℝ × ℝ) : ℝ :=
  9 * q.1 ^ 2 / s ^ 4 - 6 * q.1 * q.2 / s ^ 3 + q.2 ^ 2 / s ^ 2 - 2 / s

/- A continuous polynomial bound for the time-derivative coefficient. -/
def bellmanGaussianTimeWeight (q : ℝ × ℝ) : ℝ :=
  9 * q.1 ^ 2 + 6 * |q.1 * q.2| + q.2 ^ 2 + 2

/- The time chart has the polynomial Gaussian derivative on positive time. -/
theorem hasDerivAt_bellmanGaussianTimeChart (t : BellmanPositiveTime) (q : ℝ × ℝ) :
    HasDerivAt (fun s => bellmanGaussianTimeChart s q)
      (bellmanGaussianTimeCoefficient t.val q * bellmanGaussianKernel t q) t.val := by
  convert hasDerivAt_bellmanGaussianKernel_time t q.1 q.2 using 1
  · rfl
  · rw [(hasDerivAt_bellmanGaussianKernel_position t q.1 q.2).deriv,
      (hasDerivAt_deriv_bellmanGaussianKernel_velocity t q.1 q.2).deriv]
    dsimp [bellmanGaussianTimeCoefficient]
    field_simp [ne_of_gt t.property]
    ring

/- Sixth-order exponential decay dominates the inverse-power singularity. -/
theorem bellman_exp_neg_le_inv_six (y : ℝ) (hy : 0 < y) :
    Real.exp (-y) ≤ 720 / y ^ 6 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 6
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (-y)).le
  have hexp : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hexp] at hm
  norm_num at hm
  apply (le_div_iff₀ (pow_pos hy 6)).mpr
  nlinarith only [hm]

/- On sets away from the pole, the small-time Gaussian is bounded by a fourth power. -/
theorem bellmanGaussianKernel_le_smallTime_four (t : BellmanPositiveTime)
    (ht : t.val ≤ 1) (q : ℝ × ℝ) (a ) (ha : 0 < a)
    (hq : a ≤ q.1 ^ 2 + q.2 ^ 2) :
    bellmanGaussianKernel t q ≤
      (360 * 8 ^ 6 * Real.sqrt 3 / (Real.pi * a ^ 6)) * t.val ^ 4 := by
  have htp := t.property
  have hE : bellmanGaussianExponent t q ≤ -a / (8 * t.val) := by
    refine (bellmanGaussianExponent_le_smallTime t ht q).trans ?_
    exact div_le_div_of_nonneg_right (neg_le_neg hq) (by positivity)
  have he : Real.exp (bellmanGaussianExponent t q) ≤
      720 / (a / (8 * t.val)) ^ 6 := by
    refine (Real.exp_le_exp.mpr hE).trans ?_
    rw [neg_div]
    exact bellman_exp_neg_le_inv_six _ (by positivity)
  have hm := mul_le_mul_of_nonneg_left he
    (show 0 ≤ Real.sqrt 3 / (2 * Real.pi * t.val ^ 2) by positivity)
  unfold bellmanGaussianKernel
  refine hm.trans_eq ?_
  field_simp [ne_of_gt t.property]
  ring

/- The polynomial weight is nonnegative. -/
theorem bellmanGaussianTimeWeight_nonneg (q : ℝ × ℝ) :
    0 ≤ bellmanGaussianTimeWeight q := by
  unfold bellmanGaussianTimeWeight
  positivity

/- A small-time coefficient bound after multiplication by the fourth time power. -/
end HypoellipticAleksandrov.KineticAleksandrov
