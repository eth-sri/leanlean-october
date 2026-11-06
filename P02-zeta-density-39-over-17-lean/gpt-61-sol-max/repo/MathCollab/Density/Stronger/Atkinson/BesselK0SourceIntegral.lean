module
/-
Copyright (c) 2026 S. McColm. Selected proof slice at revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/ATKINSON_MAIN_PLUS_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain Apache-2.0.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselK0Decay
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorMass
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open Complex Filter MeasureTheory

open scoped ContDiff
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def zetaBesselK0SourceIntegrand (T G L : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  zetaSmoothDivisorTest T G L x * (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)

theorem norm_zetaBesselK0SourceIntegrand_le {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    {n : ℕ} (hn : 0 < n) (k : ℕ) (x : ℝ) :
    ‖zetaBesselK0SourceIntegrand T G L n x‖ ≤
      (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) *
        ‖zetaSmoothDivisorTest T G L x‖ := by
  by_cases hx : zetaSmoothDivisorTest T G L x = 0
  · simp only [zetaBesselK0SourceIntegrand, hx, zero_mul, norm_zero, mul_zero, le_refl]
  have hs := support_zetaSmoothDivisorTest_physical (by linarith : 0 < T) hG hL hwidth hx
  unfold zetaBesselK0SourceIntegrand
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ‖zetaSmoothDivisorTest T G L x‖ *
        (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) :=
      mul_le_mul_of_nonneg_left (abs_dfiBesselK0_source_le hT hs.1 hn k) (norm_nonneg _)
    _ = _ := mul_comm _ _


