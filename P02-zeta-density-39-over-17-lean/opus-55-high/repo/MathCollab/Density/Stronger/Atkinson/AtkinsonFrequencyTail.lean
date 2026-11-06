module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction; see third_party/twelfth/ATKINSON_CORRECTION_SERIES_MANIFEST.json.
Mathlib and the nonstationary foundations retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPowerIntegral
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFirstDerivative
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Complex MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
namespace MathCollab.Density.Stronger.Atkinson

section
variable {T b y : ℝ} (hT : 0 < T) (hy : y ∈ Icc (Real.sqrt (T / 16)) (Real.sqrt T)) (hb : 8 * Real.sqrt T ≤ b)
include T b y hT hy hb
theorem atkinsonRootSlope_far_positive :
    b ≤ atkinsonRootSlope T b y := by
  pm_1589
  have hp : 0 ≤ T / (Real.pi * y) := by positivity
  unfold atkinsonRootSlope
  grind

theorem atkinsonRootSlope_far_negative :
    atkinsonRootSlope T (-b) y ≤ -b := by
  pm_1589
  have hs : Real.sqrt (T / 16) = Real.sqrt T / 4 := by
    rw [Real.sqrt_div hT.le]
    norm_num
  have hsy : Real.sqrt T ≤ 4 * y := by rw [hs] at hy; grind
  have hp : T / (Real.pi * y) ≤ 4 * Real.sqrt T := by
    apply (div_le_iff₀ (mul_pos Real.pi_pos hy0)).2
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hprod := mul_le_mul_of_nonneg_left hsy (Real.sqrt_nonneg T)
    rw [Real.mul_self_sqrt hT.le] at hprod
    have hmul := mul_le_mul_of_nonneg_left hpi
      (show 0 ≤ 4 * Real.sqrt T * y by positivity)
    nlinarith
  unfold atkinsonRootSlope
  grind
end

theorem norm_atkinsonRootKernel_integral_far {T b c : ℝ} (hT : 0 < T)
    (hc : c ∈ Icc (Real.sqrt (T / 16)) (Real.sqrt T))
    (hb : 8 * Real.sqrt T ≤ b) :
    ‖∫ y in Real.sqrt (T / 16)..c, atkinsonRootKernel T b y‖ ≤ 1 / (b * Real.pi) ∧
    ‖∫ y in Real.sqrt (T / 16)..c, atkinsonRootKernel T (-b) y‖ ≤ 1 / (b * Real.pi) := by
  pm_6512
  pm_5873
  have hmem (y : ℝ) (hy : y ∈ Icc (Real.sqrt (T / 16)) c) :
      y ∈ Icc (Real.sqrt (T / 16)) (Real.sqrt T) := ⟨hy.1, hy.2.trans hc.2⟩
  have hd (u y : ℝ) (hy : y ∈ Icc (Real.sqrt (T / 16)) c) :
      deriv (atkinsonRootPhase T u) y = atkinsonRootSlope T u y :=
    (hasDerivAt_atkinsonRootPhase T u (ha.trans_le hy.1)).deriv
  have hmono (u : ℝ) : AntitoneOn (deriv (atkinsonRootPhase T u))
      (Icc (Real.sqrt (T / 16)) c) := by
    pm_543
  constructor
  · exact norm_phaseIntegral_le_of_positive_slope hc.1 hb0
      (fun y hy => contDiffAt_atkinsonRootPhase T b (ha.trans_le hy.1))
      (fun y hy => by rw [hd b y hy]; exact atkinsonRootSlope_far_positive hT (hmem y hy) hb)
      (hmono b)
  · exact norm_phaseIntegral_le_of_negative_slope hc.1 hb0
      (fun y hy => contDiffAt_atkinsonRootPhase T (-b) (ha.trans_le hy.1))
      (fun y hy => by rw [hd (-b) y hy]; exact atkinsonRootSlope_far_negative hT (hmem y hy) hb)
      (hmono (-b))

theorem exists_norm_atkinsonPowerIntegral_far_le (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → 8 * Real.sqrt T ≤ b →
      ‖atkinsonPowerIntegral T G L α b‖ ≤ C * G * T ^ (-α) / b ∧
      ‖atkinsonPowerIntegral T G L α (-b)‖ ≤ C * G * T ^ (-α) / b := by
  obtain ⟨C, hC, hweight⟩ := exists_intervalC1Bound_atkinsonPowerWeight α
  refine ⟨4 * C / Real.pi, by positivity, ?_⟩
  intro T G L b hT hG hGT hL hwidth hb
  pm_4342
  have hw := hf.comp_sq ha.le hab
  have hp (u : ℝ)
      (hu : ∀ x ∈ Icc (Real.sqrt (T / 16)) (Real.sqrt T),
        ‖∫ y in Real.sqrt (T / 16)..x, atkinsonRootKernel T u y‖ ≤ 1 / (b * Real.pi)) :
      ‖atkinsonPowerIntegral T G L α u‖ ≤ (4 * C / Real.pi) * G * T ^ (-α) / b := by
    have h := hw.atkinsonRoot_of_primitive_bound u ha hab hu
    rw [atkinsonPowerIntegral_eq_root hT hG hL hwidth α u, norm_mul, norm_ofNat]
    pm_4290 hfin mul_le_mul_of_nonneg_left h
    convert hfin using 1
    ring
  exact ⟨hp b (fun x hx => (norm_atkinsonRootKernel_integral_far hT hx hb).1),
    hp (-b) (fun x hx => (norm_atkinsonRootKernel_integral_far hT hx hb).2)⟩

end MathCollab.Density.Stronger.Atkinson
