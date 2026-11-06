/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic

/-! Algebraic change of basis for real diagonal Hermitian forms. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A weighted real diagonal form remains diagonal under a real connection matrix whenever its
weighted off-diagonal coefficient vanishes. This version does not normalize either diagonal
weight, so it also covers zero weights. -/
theorem real_diagonal_normSq_connection_change
    (α δ u v w x : ℝ) (f g : ℂ)
    (hcross : α * u * v + δ * w * x = 0) :
    α * Complex.normSq ((u : ℂ) * f + (v : ℂ) * g) +
        δ * Complex.normSq ((w : ℂ) * f + (x : ℂ) * g) =
      (α * u ^ 2 + δ * w ^ 2) * Complex.normSq f +
        (α * v ^ 2 + δ * x ^ 2) * Complex.normSq g := by
  have hcrossUV :
      (u * f * star (v * g)).re =
        (u * v) * (f * (starRingEnd ℂ) g).re := by
    have hv : star (v * g) = v * star g := by
      simp [mul_comm]
    calc
      (u * f * star _).re =
          (((u * v : ℝ) : ℂ) * (f * star g)).re := by
            rw [hv]
            apply congrArg Complex.re
            push_cast
            ring
      _ = (u * v) * (f * star g).re := Complex.re_ofReal_mul ..
  have hcrossWX :
      (w * f * star (x * g)).re =
        (w * x) * (f * (starRingEnd ℂ) g).re := by
    have hx : star (x * g) = x * star g := by
      simp [mul_comm]
    calc
      (w * f * star _).re =
          (((w * x : ℝ) : ℂ) * (f * star g)).re := by
            rw [hx]
            apply congrArg Complex.re
            push_cast
            ring
      _ = (w * x) * (f * star g).re := Complex.re_ofReal_mul ..
  rw [Complex.normSq_add, Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul]
  rw [Complex.normSq_ofReal, Complex.normSq_ofReal,
    Complex.normSq_ofReal, Complex.normSq_ofReal]
  simp only [Complex.star_def] at hcrossUV hcrossWX
  rw [hcrossUV, hcrossWX]
  linear_combination 2 * (f * (starRingEnd ℂ) g).re * hcross

end DOZZ.Proofs
