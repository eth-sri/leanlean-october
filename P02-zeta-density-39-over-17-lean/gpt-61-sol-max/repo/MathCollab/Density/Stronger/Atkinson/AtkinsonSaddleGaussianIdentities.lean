module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_SIGNED_NORMALIZATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonGaussianVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSaddlePhase

@[expose] public section

open Complex

namespace MathCollab.Density.Stronger.Atkinson

theorem zetaGaussianQuadraticIntegral_neg (T : ℝ) {G : ℝ} (hG : G ≠ 0) (v : ℝ) :
    zetaGaussianQuadraticIntegral T G (-v) = zetaGaussianQuadraticIntegral T G v := by
  rw [zetaGaussianQuadraticIntegral_eq T (-v) hG, zetaGaussianQuadraticIntegral_eq T v hG,
    Complex.ofReal_neg, neg_sq]

theorem zetaGaussianQuadraticIntegral_at_saddle {T : ℝ} (hT : 0 < T) (G : ℝ) (n : ℕ) :
    zetaGaussianQuadraticIntegral T G
      (Real.log (zetaAtkinsonSaddle T (Real.sqrt n)) - Real.log (T / (2 * Real.pi))) =
        atkinsonSaddleGaussian T G n := by
  rw [zetaAtkinsonSaddle_log_argument hT, atkinson_sqrt_frequency_normalized hT n]
  rfl

theorem zetaGaussianQuadraticIntegral_at_neg_saddle {T G : ℝ} (hT : 0 < T) (hG : G ≠ 0)
    (n : ℕ) :
    zetaGaussianQuadraticIntegral T G
      (Real.log (zetaAtkinsonSaddle T (-Real.sqrt n)) - Real.log (T / (2 * Real.pi))) =
        atkinsonSaddleGaussian T G n := by
  rw [zetaAtkinsonSaddle_log_argument hT, neg_div, Real.arsinh_neg, mul_neg,
    zetaGaussianQuadraticIntegral_neg T hG, atkinson_sqrt_frequency_normalized hT n]
  rfl


