/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Height.Box
import CCDN.Height.IntegerCoefficientHeight
import CCDN.Surface.CongruencePrimeWindow
import Mathlib.Algebra.MvPolynomial.PDeriv
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Determinant.PlaneSingularities
import CCDN.Height.PolynomialBoxHeight

/-! Nonsingular integer points have many smooth reduction primes
in one common finite window. The excluded primes divide one nonzero partial
derivative value, whose height is bounded directly from the equation. -/

namespace CCDN
open MvPolynomial Finset

section
variable {σ : Type*} (f : MvPolynomial σ ℤ) (j : σ)

theorem integer_pderiv_coefficient_bound 
    {H : ℝ} (hH : 0 ≤ H)
    (hcoeff : CoefficientHeightLE f H) (e : σ →₀ ℕ) :
    |((pderiv j f).coeff e : ℝ)| ≤ ((f.totalDegree : ℝ) + 1) * H := by
  rw [coeff_pderiv]
  by_cases hz : f.coeff (e + Finsupp.single j 1) = 0
  · simp [hz, zero_mul, Int.cast_zero, abs_zero]
    positivity
  · have he : e j + 1 ≤ f.totalDegree := by
      have h := ((degreeOf_le_iff).mp (degreeOf_le_totalDegree f j))
        (e + Finsupp.single j 1) (mem_support_iff.mpr hz)
      simp_all
    push_cast
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e j : ℝ) + 1)]
    have heR : (e j : ℝ) + 1 ≤ f.totalDegree + 1 := by
      exact_mod_cast (by grind)
    calc
      _ ≤ H * ((e j : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (hcoeff _) (by positivity)
      _ ≤ H * (f.totalDegree + 1) :=
        mul_le_mul_of_nonneg_left heR hH
      _ = _ := by ring

end

variable {n : ℕ} (f : MvPolynomial (Fin n) ℤ)

theorem integer_pderiv_log_bound
    (j : Fin n) {H B : ℝ}
    (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (x : IntPoint n) (hx : InBox x B)
    (hne : eval x (pderiv j f) ≠ 0) :
    Real.log |(eval x (pderiv j f) : ℝ)| ≤
      (n + 1 : ℝ) * Real.log ((f.totalDegree : ℝ) + 1) +
        Real.log H + f.totalDegree * Real.log B := by
  have hpos : (0 : ℝ) < |(eval x (pderiv j f) : ℝ)| :=
    abs_pos.mpr (mod_cast hne)
  have hdpos : (0 : ℝ) < f.totalDegree + 1 := by positivity
  have hH0 : 0 < H := by linarith
  have hB0 : 0 < B := by linarith
  have hlog := Real.log_le_log hpos
    (show |(eval x (pderiv j f) : ℝ)| ≤
          ((f.totalDegree : ℝ) + 1) ^ (n + 1) * H * B ^ f.totalDegree by
        have hb := polynomial_eval₂_box_bound (pderiv j f)
          (((f.totalDegree : ℝ) + 1) * H) B (by positivity) hB
          (integer_pderiv_coefficient_bound f j hH0.le hcoeff)
          (fun i => (x i : ℝ)) hx
        have heval : (eval x (pderiv j f) : ℝ) =
            eval₂ (Int.castRingHom ℝ) (fun i => (x i : ℝ)) (pderiv j f) := by
          simpa [eval₂_id, RingHom.comp_id, Function.comp_def, Int.coe_castRingHom] using
            eval₂_comp_left (Int.castRingHom ℝ) (RingHom.id ℤ) x (pderiv j f)
        rw [← heval, Fintype.card_fin] at hb
        have hdeg : (pderiv j f).totalDegree ≤ f.totalDegree := by
          rw [← rational_map_totalDegree (pderiv j f), ← pderiv_map]
          exact (pderiv_totalDegree_le (map (Int.castRingHom ℚ) f) j).trans
            (by rw [rational_map_totalDegree]; omega)
        have hdegR : ((pderiv j f).totalDegree : ℝ) ≤ f.totalDegree := mod_cast hdeg
        calc
          _ ≤ (((pderiv j f).totalDegree : ℝ) + 1) ^ n *
              (((f.totalDegree : ℝ) + 1) * H) * B ^ (pderiv j f).totalDegree := hb
          _ ≤ (f.totalDegree + 1) ^ n *
              (((f.totalDegree : ℝ) + 1) * H) * B ^ f.totalDegree := by
            gcongr
          _ = _ := by grind)
  rw [Real.log_mul (mul_pos (pow_pos hdpos _) hH0).ne' (pow_pos hB0 _).ne',
    Real.log_mul (pow_pos hdpos _).ne' hH0.ne', Real.log_pow, Real.log_pow] at hlog
  simpa using hlog

