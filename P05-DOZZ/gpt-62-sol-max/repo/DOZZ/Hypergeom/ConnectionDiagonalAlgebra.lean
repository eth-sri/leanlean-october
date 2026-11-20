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
  have hre (r s : ℝ) :
      ((r : ℂ) * f * (starRingEnd ℂ) ((s : ℂ) * g)).re = r * s * (f * (starRingEnd ℂ) g).re := by
    rw [map_mul, Complex.conj_ofReal]
    rw [show (r : ℂ) * f * ((s : ℂ) * (starRingEnd ℂ) g) =
      ((r * s : ℝ) : ℂ) * (f * (starRingEnd ℂ) g) by push_cast; ring, Complex.re_ofReal_mul]
  simp only [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal, hre]
  linear_combination 2 * (f * (starRingEnd ℂ) g).re * hcross

end DOZZ.Proofs
