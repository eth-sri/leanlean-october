module
import Mathlib
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSaddleNormalization
public import MathCollab.Density.Stronger.Atkinson.AtkinsonIndexPhase

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The stationary Atkinson phase at both actual saddles

The phase uses the stationary `-pi/4` convention of Heath--Brown (1978), (11).
Ivić's Orsay (6.22) omits that constant: AtkinsonPrintedSource proves the
explicit constant-phase and unit-modulus prefix bridges, rather than
asserting literal equality with that printed phase.
Its definition follows the already inspected adjacent GafniTao
HeathBrownAtkinsonPhase module; no conditional moment theorem is imported.
The equalities below connect it to the actual continuous source phase.
-/



namespace MathCollab.Density.Stronger.Atkinson

section
variable {T : ℝ} (hT : 0 < T) (n : ℕ)
include T hT n

theorem atkinson_sqrt_frequency_normalized  :
    Real.sqrt (n : ℝ) / (2 * Real.sqrt (T / (2 * Real.pi))) =
      Real.sqrt (Real.pi * (n : ℝ) / (2 * T)) := by
  have hA : 0 < T / (2 * Real.pi) := by positivity
  have he : (Real.sqrt (n : ℝ) / (2 * Real.sqrt (T / (2 * Real.pi)))) ^ 2 =
      Real.pi * (n : ℝ) / (2 * T) := by grind
  exact (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2 he.symm |>.symm

theorem atkinson_sqrt_frequency_radical  :
    Real.pi * Real.sqrt (n : ℝ) * Real.sqrt ((Real.sqrt (n : ℝ)) ^ 2 +
      4 * (T / (2 * Real.pi))) =
      Real.sqrt (2 * Real.pi * (n : ℝ) * T + Real.pi ^ 2 * (n : ℝ) ^ 2) := by
  have he : (Real.pi * Real.sqrt (n : ℝ) * Real.sqrt ((Real.sqrt (n : ℝ)) ^ 2 +
      4 * (T / (2 * Real.pi)))) ^ 2 =
      2 * Real.pi * (n : ℝ) * T + Real.pi ^ 2 * (n : ℝ) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (by positivity)]
    grind
  exact (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2 he.symm |>.symm

theorem atkinsonDualPhase_sqrt  :
    atkinsonDualPhase T (Real.sqrt n) = atkinsonSourcePhase T n + Real.pi / 4 := by
  unfold atkinsonDualPhase atkinsonSourcePhase
  rw [atkinson_sqrt_frequency_normalized hT n, atkinson_sqrt_frequency_radical hT n]
  ring

theorem zetaAtkinsonPhase_saddle_sqrt  :
    zetaAtkinsonPhase T (Real.sqrt n) (zetaAtkinsonSaddle T (Real.sqrt n)) =
      atkinsonCentralPhase T + Real.pi * n + atkinsonSourcePhase T n + Real.pi / 4 := by
  rw [zetaAtkinsonPhase_at_saddle hT, atkinsonDualPhase_sqrt hT n,
    Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

theorem zetaAtkinsonPhase_saddle_neg_sqrt  :
    zetaAtkinsonPhase T (-Real.sqrt n) (zetaAtkinsonSaddle T (-Real.sqrt n)) =
      atkinsonCentralPhase T + Real.pi * n - atkinsonSourcePhase T n - Real.pi / 4 := by
  rw [zetaAtkinsonPhase_at_saddle hT, atkinsonDualPhase_neg, atkinsonDualPhase_sqrt hT n,
    neg_sq, Real.sq_sqrt (Nat.cast_nonneg n)]
  ring
end


theorem exp_atkinson_natural_pi (n : ℕ) :
    Complex.exp (((Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I) = (-1 : ℂ) ^ n := by
  rw [show (((Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I) =
    (n : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_nat_mul, Complex.exp_pi_mul_I]

section
variable {T : ℝ} (hT : 0 < T) (n : ℕ)
include T hT n

theorem exp_zetaAtkinsonPhase_saddle_sqrt  :
    Complex.exp ((zetaAtkinsonPhase T (Real.sqrt n)
      (zetaAtkinsonSaddle T (Real.sqrt n)) : ℂ) * Complex.I) =
      Complex.exp ((atkinsonCentralPhase T : ℂ) * Complex.I) * (-1 : ℂ) ^ n *
        Complex.exp (((atkinsonSourcePhase T n + Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
  rw [zetaAtkinsonPhase_saddle_sqrt hT n, ← exp_atkinson_natural_pi,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem exp_zetaAtkinsonPhase_saddle_neg_sqrt  :
    Complex.exp ((zetaAtkinsonPhase T (-Real.sqrt n)
      (zetaAtkinsonSaddle T (-Real.sqrt n)) : ℂ) * Complex.I) =
      Complex.exp ((atkinsonCentralPhase T : ℂ) * Complex.I) * (-1 : ℂ) ^ n *
        Complex.exp (((-atkinsonSourcePhase T n - Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
  rw [zetaAtkinsonPhase_saddle_neg_sqrt hT n, ← exp_atkinson_natural_pi,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring
end



