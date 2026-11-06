module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonAmplitudeIntegral
import WeylPort.Analytic.RealLaplace

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Reciprocal-window tails of the actual stationary integral

Both signs of the slope are derived from the actual positive root.
The weighted bounds use the proved total variation, independently of the
natural-scale C2 estimate used in the central window.
-/


open Complex MeasureTheory Set
open scoped ContDiff

namespace MathCollab.Density.Stronger.Atkinson

theorem IntervalC1Bound.restrict {f : ℝ → ℂ} {a c u v M : ℝ}
    (hf : IntervalC1Bound f a c M) (hau : a ≤ u) (huv : u ≤ v) (hvc : v ≤ c) :
    IntervalC1Bound f u v M := by
  pm_4401
  refine ⟨hf.nonneg, fun x hx => hf.smooth x (hmem hx),
    fun x hx => hf.norm_le x (hmem hx), ?_⟩
  exact (intervalIntegral.integral_mono_interval hau huv hvc
    (Filter.Eventually.of_forall (fun x => norm_nonneg (deriv f x)))
    (hf.derivative_integrable (hau.trans (huv.trans hvc))).norm).trans hf.variation_le

section
variable {T b y H : ℝ} (hT : 0 < T) (hy : 0 < y) (hH : 0 ≤ H)
include T b y H hT hy hH
theorem atkinsonRootSlope_le_neg_window
    (hr : atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ y) :
    atkinsonRootSlope T b y ≤ -2 * H := by
  pm_4381
  pm_1178

theorem window_le_atkinsonRootSlope
    (hr : y ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H) :
    2 * H ≤ atkinsonRootSlope T b y := by
  pm_4381
  pm_1179
end

section
variable {T b a c H : ℝ} (hT : 0 < T) (ha : 0 < a) (hac : a ≤ c) (hH : 0 < H)
include T b a c H hT ha hac hH
theorem norm_atkinsonRootKernel_integral_right_window
    (hr : atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ a) :
    ‖∫ y in a..c, atkinsonRootKernel T b y‖ ≤ 1 / (2 * H * Real.pi) := by
  pm_4402
  pm_5536 norm_phaseIntegral_le_of_negative_slope
  · intro y hy
    rw [hd y hy]
    simpa only [neg_mul] using atkinsonRootSlope_le_neg_window hT
      (ha.trans_le hy.1) hH.le (hr.trans hy.1)
  pm_4403

theorem norm_atkinsonRootKernel_integral_left_window
    (hr : c ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H) :
    ‖∫ y in a..c, atkinsonRootKernel T b y‖ ≤ 1 / (2 * H * Real.pi) := by
  pm_4402
  pm_5536 norm_phaseIntegral_le_of_positive_slope
  · intro y hy
    rw [hd y hy]
    exact window_le_atkinsonRootSlope hT (ha.trans_le hy.1) hH.le (hy.2.trans hr)
  pm_4403
end

section
variable {f : ℝ → ℂ} {a c M T H : ℝ} (hf : IntervalC1Bound f a c M) (hT : 0 < T) (b : ℝ) (ha : 0 < a)
include f a c M T H hf hT b ha
theorem IntervalC1Bound.atkinsonRoot_right_window (hac : a ≤ c) (hH : 0 < H)
    (hr : atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ a) :
    ‖∫ y in a..c, f y * atkinsonRootKernel T b y‖ ≤ M / (H * Real.pi) := by
  apply (hf.atkinsonRoot_of_primitive_bound b ha hac
    (fun x hx => norm_atkinsonRootKernel_integral_right_window hT ha hx.1 hH hr)).trans_eq
  ring

theorem IntervalC1Bound.atkinsonRoot_left_window (hac : a ≤ c) (hH : 0 < H)
    (hr : c ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H) :
    ‖∫ y in a..c, f y * atkinsonRootKernel T b y‖ ≤ M / (H * Real.pi) := by
  apply (hf.atkinsonRoot_of_primitive_bound b ha hac
    (fun x hx => norm_atkinsonRootKernel_integral_left_window hT ha hx.1 hH
      (hx.2.trans hr))).trans_eq
  ring

theorem IntervalC1Bound.atkinsonRoot_sub_local (hH : 0 < H)
    (hleft : a ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)
    (hright : atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ c) :
    ‖(∫ y in a..c, f y * atkinsonRootKernel T b y) -
      ∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
        (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), f y * atkinsonRootKernel T b y‖ ≤
      2 * M / (H * Real.pi) := by
  pm_4412
  have huv : r - H ≤ r + H := by linarith
  have hi {u v : ℝ} (hau : a ≤ u) (huv' : u ≤ v) (hvc : v ≤ c) :
      IntervalIntegrable (fun y => f y * atkinsonRootKernel T b y) volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv']
    exact fun y hy => ((hf.smooth y ⟨hau.trans hy.1, hy.2.trans hvc⟩).continuousAt.mul
      (continuousAt_atkinsonRootKernel T b (ha.trans_le (hau.trans hy.1)))).continuousWithinAt
  have hlow := (hf.restrict le_rfl hleft (huv.trans hright)).atkinsonRoot_left_window
    hT b ha hleft hH (show r - H ≤ r - H from le_rfl)
  have hhigh := (hf.restrict (hleft.trans huv) hright le_rfl).atkinsonRoot_right_window
    hT b (ha.trans_le (hleft.trans huv)) hright hH (show r + H ≤ r + H from le_rfl)
  have he : (∫ y in a..c, f y * atkinsonRootKernel T b y) -
      (∫ y in (r - H)..(r + H), f y * atkinsonRootKernel T b y) =
      (∫ y in a..(r - H), f y * atkinsonRootKernel T b y) +
        ∫ y in (r + H)..c, f y * atkinsonRootKernel T b y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hi le_rfl hleft (huv.trans hright)) (hi hleft (huv.trans hright) le_rfl),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hi hleft huv hright) (hi (hleft.trans huv) hright le_rfl)]
    ring
  change ‖(∫ y in a..c, f y * atkinsonRootKernel T b y) -
    (∫ y in (r - H)..(r + H), f y * atkinsonRootKernel T b y)‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans ((add_le_add hlow hhigh).trans_eq ?_)
  ring
end

end MathCollab.Density.Stronger.Atkinson
