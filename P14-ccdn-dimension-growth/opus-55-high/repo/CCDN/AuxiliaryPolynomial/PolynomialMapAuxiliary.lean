/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.Nonmultiple
import CCDN.Determinant.HeightDeterminant
import CCDN.Height.CountingHypotheses
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryDegree
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryLargeHeight
import CCDN.Determinant.PolynomialMapDeterminant

/-!
Auxiliary nonmultiples and explicit degree choices for polynomial images
of the original integer plane curve. Sharp finite-field counts remain explicit.

Explicit integer degree choices for both coefficient-height ranges.
-/

namespace CCDN

/-- For nonnegative reals `l` and `R`, there is an integer `M` with `d ≤ M`, `l ≤ M`, `R < M` and
`M ≤ d + l + R + 2`. -/
lemma auxiliary_integer_degree_selection (d : ℕ) {l R : ℝ} (hl : 0 ≤ l) (hR : 0 ≤ R) :
    ∃ M : ℕ, d ≤ M ∧ l ≤ M ∧ R < M ∧ (M : ℝ) ≤ d + l + R + 2 := by
  refine ⟨d + ⌈l⌉₊ + ⌊R⌋₊ + 1, by omega, ?_, ?_, ?_⟩
  · have h := Nat.le_ceil l
    grind
  · have h := Nat.lt_floor_add_one R
    grind
  · have hc := Nat.ceil_lt_add_one hl
    have hf := Nat.floor_le hR
    push_cast
    linarith


variable {d t : ℕ} (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ) (hf0 : f ≠ 0) (hd : 0 < d) {H B C : ℝ} (hH : 1 ≤ H) (hB : 1 ≤ B) (x : Fin t → Fin 3 → ℤ) (hcomp : ∀ M, d ≤ M → (∀ g : MvPolynomial (Fin 3) ℤ, g.IsHomogeneous M → (∀ i, MvPolynomial.eval (x i) g = 0) → f ∣ g) →
    ∃ s : ℕ, 2 * s + d ^ 2 = d * (2 * M + 3) ∧
      (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
        Real.log (1 + Real.log H / (d : ℝ) ^ 2) - heightDeterminantError C) ≤
        Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
          s * M * Real.log B -
          (((2 + M).choose M : ℝ) - s) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)|)
include hf0 hd hH hB hcomp

/-- Small-height auxiliary form: given the no-auxiliary height comparison for the points `x i`,
there is an auxiliary form of explicitly bounded degree `M` through all of them. -/
theorem auxiliary_small_height_degree
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 4 * d * Real.log B) :
    ∃ M : ℕ, (M : ℝ) ≤ d + Real.log B +
      2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
        (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
          |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) + 2 ∧
      ∃ g, IsPointAuxiliary f g M x := by
  let R := 2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
    (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
      |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2)
  have := Real.log_nonneg hH
  obtain ⟨M, hdM, hML, hth, hM⟩ := auxiliary_integer_degree_selection d (Real.log_nonneg hB)
    (show 0 ≤ R by positivity)
  refine ⟨M, hM, ?_⟩
  by_contra hnone
  obtain ⟨s, hr, hc⟩ := hcomp M hdM (dvd_of_not_exists_isPointAuxiliary hnone)
  have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hlog := plane_auxiliary_log_degree_bound hd hdM hr hB hL hML hheight hc
  exact (not_lt_of_ge (plane_degree_bound_of_log_bound hd (hd.trans_le hdM)
    (by linarith) (by linarith) (by positivity) hlog)) hth

/-- Large-height auxiliary form: given the no-auxiliary height comparison for the points `x i`,
with `4 d log B ≤ log H` and `H` at most the leading coefficient of `f` times `exp (T d²)`,
there is an auxiliary form through all of them of degree at most
`(34 + 8 exp (heightDeterminantError C + 6 + T)) d³`. -/
theorem auxiliary_large_height_degree
    (T : ℝ) (hT : 0 ≤ T)
    (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * (d : ℝ) ^ 2) :
    ∃ M : ℕ, (M : ℝ) ≤ (34 + 8 * Real.exp (heightDeterminantError C + 6 + T)) * (d : ℝ) ^ 3 ∧
      ∃ g, IsPointAuxiliary f g M x := by
  let R := 8 * Real.exp (heightDeterminantError C + 6 + T) * d ^ 3
  obtain ⟨M, hMlarge, _, hth, hM⟩ := auxiliary_integer_degree_selection (32 * d)
    (show (0 : ℝ) ≤ 0 from le_rfl) (show 0 ≤ R by positivity)
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hd3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith
  have hd31 := hd1.trans hd3
  refine ⟨M, by grind, ?_⟩
  have hdM : d ≤ M := by omega
  by_contra hnone
  obtain ⟨s, hr, hc⟩ := hcomp M hdM (dvd_of_not_exists_isPointAuxiliary hnone)
  have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hlog := plane_auxiliary_large_height_log_bound hd hMlarge hr hB hL hH hT hheight
    hposition hc
  exact (not_lt_of_ge (plane_large_degree_bound_of_log_bound hd (hd.trans_le hdM) hlog)) hth
