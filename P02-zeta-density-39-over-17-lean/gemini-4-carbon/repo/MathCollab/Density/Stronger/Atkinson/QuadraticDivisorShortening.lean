module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.QuadraticDivisorBand
public import MathCollab.Density.Stronger.Atkinson.FrozenWindow

@[expose] public section

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem norm_zetaFrozenDivisorQuadraticSum_sub_short_le {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 ≤ L) :
    ‖zetaFrozenDivisorQuadraticSum T G - zetaShortQuadraticDivisorSum T G L‖ ≤
      (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖) *
        (Real.sqrt Real.pi * G * Real.exp (-L ^ 2 / 8)) := by
  classical
  let S := zetaQuadraticDivisorBand T G L
  let f := fun n : ℕ => zetaFrozenDivisorCoefficient T n * zetaSquareReflectedGammaPhase T *
    zetaGaussianQuadraticIntegral T G (Real.log (n : ℝ) - Real.log (T / (2 * Real.pi)))
  let B := Real.sqrt Real.pi * G * Real.exp (-L ^ 2 / 8)
  have hf : Summable f := summable_zetaFrozenDivisorQuadraticTerm hT hG hGT
  have hc := summable_norm_zetaFrozenDivisorCoefficient hT
  have hpoint (n : {n : ℕ // n ∉ S}) : ‖f n‖ ≤ ‖zetaFrozenDivisorCoefficient T n‖ * B :=
    norm_zetaQuadraticDivisorTerm_off_band_le hT hG hGT hL n.2
  change ‖(∑' n, f n) - ∑ n ∈ S, f n‖ ≤ _
  rw [← hf.sum_add_tsum_subtype_compl S, add_sub_cancel_left]
  calc
    _ ≤ ∑' n : {n : ℕ // n ∉ S}, ‖f n‖ := norm_tsum_le_tsum_norm (hf.norm.subtype _)
    _ ≤ ∑' n : {n : ℕ // n ∉ S}, ‖zetaFrozenDivisorCoefficient T n‖ * B :=
      (hf.norm.subtype _).tsum_le_tsum hpoint ((hc.subtype _).mul_right B)
    _ = (∑' n : {n : ℕ // n ∉ S}, ‖zetaFrozenDivisorCoefficient T n‖) * B := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Summable.tsum_subtype_le (fun n : ℕ => ‖zetaFrozenDivisorCoefficient T n‖)
        (fun n => n ∉ S) (fun _ => norm_nonneg _) hc) (by dsimp [B]; positivity)

/-- The omitted source has a uniform square-root coefficient factor,
not a height-dependent constant chosen after the Gaussian width. -/
theorem exists_norm_zetaFrozenDivisorQuadraticSum_sub_short_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T → 0 ≤ L →
      ‖zetaFrozenDivisorQuadraticSum T G - zetaShortQuadraticDivisorSum T G L‖ ≤
        C * T ^ (1 / 2 + ε) * G * Real.exp (-L ^ 2 / 8) := by
  obtain ⟨C, hC, hmass⟩ := exists_tsum_norm_source_divisor_weight_le ε hε
  refine ⟨C * Real.sqrt Real.pi, by positivity, ?_⟩
  intro T G L hT hG hGT hL
  apply (norm_zetaFrozenDivisorQuadraticSum_sub_short_le (by linarith) hG hGT hL).trans
  have hm : (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖) ≤ C * T ^ (1 / 2 + ε) := by
    simpa only [zetaFrozenDivisorCoefficient, norm_mul] using hmass T hT (-T)
  calc
    _ ≤ (C * T ^ (1 / 2 + ε)) * (Real.sqrt Real.pi * G * Real.exp (-L ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ = _ := by ring

end MathCollab.Density.Stronger.Atkinson
