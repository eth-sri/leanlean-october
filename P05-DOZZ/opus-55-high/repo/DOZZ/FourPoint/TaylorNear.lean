/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorOneRootIdentity
public import DOZZ.FourPoint.TaylorNearKernel
public import DOZZ.FourPoint.TaylorRadialBall

/-! The near-root positive Taylor contribution from weighted Jensen and one insertion. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A uniform near-root bound for the actual supplied GMC. The same fixed disk controls the
inserted inverse moment; the planar radial exponent exceeds -2 for every positive gamma. -/
theorem twoRooted_near_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 / 4 →
      ∀ d : ℝ, 0 < d → d ≤ ‖z‖ / 2 →
        gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p z (Metric.ball z d) ≤
          ENNReal.ofReal (C * ‖z‖ ^ (-γ * α₁) * d ^ (γ ^ 2 / 2)) := by
  obtain ⟨C₀, hC₀, hsp⟩ := twoRooted_annular_spatial_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hp
  obtain ⟨C₁, hC₁, hball⟩ := planar_radial_ball_bound (γ ^ 2 / 2 - 2)
    (by simp_all)
  let k : ℝ := 2 ^ (|γ * α₁| + |γ * α₂|)
  let C := C₀ * k * C₁
  refine ⟨C, by positivity, ?_⟩
  intro z hz hz4 d hd hdsmall
  have hzpos := norm_pos_iff.mpr hz
  have hnear (x : ℂ) (hx : x ∈ Metric.ball z d) : ‖x - z‖ ≤ ‖z‖ / 2 :=
    (show ‖x - z‖ < d by simpa only [Metric.mem_ball, dist_eq_norm] using hx).le.trans hdsmall
  have hunit (x : ℂ) (hx : x ∈ Metric.ball z d) : ‖x‖ ≤ 1 / 2 := by
    linarith only [(norm_sub_norm_le x z), (hnear x hx), hz4]
  have hkernel : (∫⁻ x in Metric.ball z d, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2)) ≤
      ENNReal.ofReal (k * ‖z‖ ^ (-γ * α₁)) * ENNReal.ofReal (C₁ * d ^ (γ ^ 2 / 2)) := by
    have he : γ ^ 2 / 2 - 2 + 2 = γ ^ 2 / 2 := by ring
    calc
      _ ≤ ∫⁻ x in Metric.ball z d, ENNReal.ofReal _ *
          ENNReal.ofReal _ :=
        setLIntegral_mono' measurableSet_ball (fun x hx => gammaHalf_near_kernel_bound
          γ α₁ α₂ α₃ hγ z x hz hz4 (hnear x hx))
      _ = ENNReal.ofReal _ *
          (∫⁻ x in Metric.ball z d, ENNReal.ofReal _) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul' le_rfl (by grind)
  calc
    _ ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal _ * ENNReal.ofReal _) :=
      (hsp z hz4 _ measurableSet_ball hunit).trans (mul_le_mul' le_rfl hkernel)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC₀.le]
      congr 1
      ring

end DOZZ.Proofs
