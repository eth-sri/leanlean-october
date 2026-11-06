module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaQuadraticKernel
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Integration by parts for a quadratic Taylor remainder

A factor z squared removes the stationary singularity. The estimate uses
the actual smooth coefficient and its derivative, with no omitted endpoint.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

set_option hygiene false in
macro "pb_2543" : tactic => `(tactic| (
  intro z
  have h := ((hasDerivAt_id z).mul
    (hV.differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0) z).hasDerivAt).ofReal_comp))
theorem norm_integral_sq_mul_betaQuadraticKernel_le
    {V : ℝ → ℝ} {T H M L : ℝ}
    (hV : ContDiff ℝ ∞ V) (hT : 0 < T) (hH : 0 < H)
    (hb : ∀ z : ℝ, |V z| ≤ M) (hd : ∀ z : ℝ, |deriv V z| ≤ L) :
    ‖∫ z in (-H)..H, ((z^2*V z : ℝ) : ℂ)*betaQuadraticKernel T z‖ ≤
      (2*H*M+2*H*(M+H*L))/(2*Real.pi*T) := by
  pm_1635
  have hU : ∀ z : ℝ, HasDerivAt U (U' z) z := by
    pb_2543
    aesop
  pm_1633
  have hUb : ∀ z : ℝ, |z| ≤ H → ‖U z*betaQuadraticKernel T z‖ ≤ H*M := by
    intro z hz
    pm_502 norm_mul norm_betaQuadraticKernel mul_one Complex.norm_real Real.norm_eq_abs abs_mul
    exact mul_le_mul hz (hb z) (abs_nonneg _) hH.le
  have hIb : ‖∫ z in (-H)..H, U' z*betaQuadraticKernel T z‖ ≤ 2*H*(M+H*L) := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -H) (b := H) (f := fun z : ℝ => U' z*betaQuadraticKernel T z) (C := M+H*L) (fun z hz => by
        pm_1636
        exact (abs_add_le (V z) (z*deriv V z)).trans
          (add_le_add (hb z) (by
            rw [abs_mul]
            exact mul_le_mul hz' (hd z) (abs_nonneg _) hH.le)))
    pm_6210
  pm_1634

end TaoTrudgianYang2025
