module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Real Laplace moments and exponential tails

These estimates control the discarded tails in the negative-axis Euler integral.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open MeasureTheory Set Filter Asymptotics

/- The positive Gamma moment kernel at Laplace scale X. -/
def laplaceMoment (a X t : ℝ) : ℝ := t ^ (a - 1) * Real.exp (-(X * t))

/- The positive-scale Gamma moment is integrable. -/
theorem integrable_laplaceMoment (a X : ℝ) (ha : 0 < a) (hX : 0 < X) :
    IntegrableOn (laplaceMoment a X) (Ioi 0) volume := by
  change IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(X * t))) (Ioi 0) volume
  simpa only [Real.rpow_one, neg_mul] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1)
      (b := X) (by linarith only [ha]) zero_lt_one hX

/- Nonnegativity of the moment kernel. -/
theorem laplaceMoment_nonneg (a X t : ℝ) (ht : 0 ≤ t) : 0 ≤ laplaceMoment a X t :=
  mul_nonneg (Real.rpow_nonneg ht _) (Real.exp_pos _).le

/- The full Gamma moment at positive Laplace scale. -/
theorem integral_laplaceMoment (a X : ℝ) (ha : 0 < a) (hX : 0 < X) :
    (∫ t in Ioi (0 : ℝ), laplaceMoment a X t) = X ^ (-a) * Real.Gamma a := by
  change (∫ t in Ioi (0 : ℝ), t ^ (a - 1) * Real.exp (-(X * t))) = _
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hX,
    one_div, Real.inv_rpow hX.le, Real.rpow_neg hX.le]

/- Pointwise exponential gain on the discarded half-line. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
