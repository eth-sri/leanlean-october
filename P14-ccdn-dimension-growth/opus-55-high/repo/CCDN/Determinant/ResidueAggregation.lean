/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.LocalDeterminant
import CCDN.Determinant.HypersurfaceLocalDeterminant
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Aggregating the local determinant exponents for curves

Cauchy–Schwarz preserves the leading quadratic coefficient when residue classes
have different multiplicities. These are the numerical aggregation steps in the
curve case of CCDN Proposition 2.6. The geometric local divisibility and
finite-field multiplicity estimates are not part of this module.
-/

namespace CCDN

variable {ι : Type*} [Fintype ι] (n : ℕ) (s μ : ι → ℕ) (hμ : ∀ i, 0 < μ i)
include hμ

/-- A common cutoff aggregates without any loss in the leading coefficient. -/
theorem aggregate_hypersurface_exponents_cutoff
    (K : ℕ) :
    (∑ i, s i) * K ≤ (∑ i, hypersurfaceMultiplicityExponent (n + 1) (μ i) (s i)) +
      (∑ i, μ i) * (n + 1 + K).choose (n + 2) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    hypersurfaceMultiplicityExponent_cutoff n (s i) K (hμ i))
  simpa [Finset.sum_add_distrib, ← Finset.sum_mul] using h

omit hμ in
/-- Optimizing the curve cutoff gives the sharp quadratic leading constant. -/
theorem cutoff_exponent_lower {s e T : ℕ} (hpos : 0 < T)
    (hK : ∀ K : ℕ, s * K ≤ e + T * (1 + K).choose 2) :
    (s : ℝ) ^ 2 / (2 * T) - s ≤ e := by
  have h := hK (s / T)
  have hc := Nat.add_one_mul_choose_eq (s / T) 1
  have hdm := Nat.div_add_mod s T
  have hlt := Nat.mod_lt s hpos
  simp [Nat.choose_one_right, add_comm 1, Nat.reduceAdd] at h hc
  have key : s ^ 2 ≤ 2 * T * e + 2 * T * s := by
    generalize s / T = q at h hc hdm
    generalize s % T = r at hdm hlt
    subst hdm
    nlinarith [Nat.mul_le_mul_left (2 * T) h, congrArg (T * T * ·) hc, Nat.mul_le_mul_left r hlt.le]
  have hT : (0 : ℝ) < T := mod_cast hpos
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
  have := (Nat.cast_le (α := ℝ)).mpr key
  push_cast at this
  linarith

end CCDN
