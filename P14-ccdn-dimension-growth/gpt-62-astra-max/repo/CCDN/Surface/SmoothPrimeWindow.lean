/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Height.Box
public import CCDN.Height.IntegerCoefficientHeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
import CCDN.Algebra.FieldMapIrreducible
import CCDN.Determinant.PlaneSingularities
import CCDN.Height.PolynomialBoxHeight

/-! Height of a nonzero partial derivative on the integer box. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

variable {n : ℕ} (f : IntegerPolynomial n) (j : Fin n) {H B : ℝ} {σ : Type*}

private theorem integer_pderiv_coefficient_bound [Fintype σ]
    (f : MvPolynomial σ ℤ) (j : σ) {H : ℝ} (hH : 0 ≤ H)
    (hcoeff : CoefficientHeightLE f H) (e : σ →₀ ℕ) :
    |((pderiv j f).coeff e : ℝ)| ≤ ((f.totalDegree : ℝ) + 1) * H := by
  classical
  rw [coeff_pderiv]
  by_cases hz : f.coeff (e + Finsupp.single j 1) = 0
  · simp only [hz, zero_mul, Int.cast_zero, abs_zero]
    positivity
  · have he := by
      have h := (degreeOf_le_iff.mp (degreeOf_le_totalDegree f j))
        (e + Finsupp.single j 1) (mem_support_iff.mpr hz)
      simpa using h
    push_cast
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e j : ℝ) + 1)]
    have heR : (e j : ℝ) + 1 ≤ (f.totalDegree : ℝ) + 1 := by
      exact_mod_cast (by omega)
    calc
      _ ≤ H * ((e j) + 1) :=
        mul_le_mul_of_nonneg_right (hcoeff _) (by positivity)
      _ ≤ H * (f.totalDegree + 1) :=
        mul_le_mul_of_nonneg_left heR hH
      _ = _ := by ring

private theorem integer_pderiv_totalDegree_le
    (f : MvPolynomial σ ℤ) (j : σ) :
    (pderiv j f).totalDegree ≤ f.totalDegree := by
  rw [← rational_map_totalDegree _, ← pderiv_map]
  grind [pderiv_totalDegree_le, rational_map_totalDegree]

private theorem integer_pderiv_evaluation_bound
    (hH : 0 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (x : IntPoint n) (hx : InBox x B) :
    |(eval x (pderiv j f) : ℝ)| ≤
      ((f.totalDegree : ℝ) + 1) ^ (n + 1) * H * B ^ f.totalDegree := by
  have hb := polynomial_eval₂_box_bound _
    _ B (by positivity) hB
    (integer_pderiv_coefficient_bound f j hH hcoeff)
    (fun i => (x i)) hx
  have heval := by
    simpa [Function.comp_def] using
      eval₂_comp_left (Int.castRingHom ℝ) (RingHom.id ℤ) x (pderiv j f)
  rw [← heval, Fintype.card_fin] at hb
  have hdeg := integer_pderiv_totalDegree_le f j
  calc
    _ ≤ (((pderiv j f).totalDegree) + 1) ^ n *
        ((f.totalDegree + 1) * H) * B ^ (pderiv j f).totalDegree := hb
    _ ≤ (f.totalDegree + 1) ^ n *
        ((f.totalDegree + 1) * H) * B ^ f.totalDegree := by
      gcongr
    _ = _ := by ring

theorem integer_pderiv_log_bound
    (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (x : IntPoint n) (hx : InBox x B)
    (hne : eval x (pderiv j f) ≠ 0) :
    Real.log |(eval x (pderiv j f) : ℝ)| ≤
      (n + 1 : ℝ) * Real.log ((f.totalDegree : ℝ) + 1) +
        Real.log H + f.totalDegree * Real.log B := by
  have hdpos : (0 : ℝ) < (f.totalDegree : ℝ) + 1 := by positivity
  have hH0 : 0 < H := by linarith
  have hB0 : 0 < B := by linarith
  have hlog := Real.log_le_log (abs_pos.mpr (by exact_mod_cast hne))
    (integer_pderiv_evaluation_bound f j hH0.le hB hcoeff x hx)
  simp_all [Real.log_mul (mul_pos _ hH0).ne' (pow_pos hB0 _).ne', Real.log_mul (pow_pos hdpos _).ne' hH0.ne']

end
end CCDN
