/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

public import CCDN.Height.Box
public import CCDN.Height.IntegerCoefficientHeight
public import CCDN.Surface.CongruencePrimeWindow
public import Mathlib.Algebra.MvPolynomial.PDeriv
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Determinant.PlaneSingularities
import CCDN.Height.PolynomialBoxHeight

/-! Nonsingular integer points have many smooth reduction primes
in one common finite window. The excluded primes divide one nonzero partial
derivative value, whose height is bounded directly from the equation. -/

public section
namespace CCDN
open MvPolynomial Finset



variable {n : ℕ} (f : CCDN.IntegerPolynomial n)


/-- If `x` is an integer point of the box at which some partial derivative of `f` is nonzero,
and `L` dominates the logarithmic size of such a derivative, then the prime window of
logarithmic size `L` contains a set of primes with product at least `exp L` modulo each of
which `x` is a smooth point of `f`. -/
theorem exists_smooth_prime_window_subset  {H B L : ℝ}
    (hH : 1 ≤ H) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hcoeff : CoefficientHeightLE f H)
    (hheight : (n + 1 : ℝ) * Real.log (↑f.totalDegree + 1) +
      Real.log H + f.totalDegree * Real.log B ≤ L)
    (x : IntPoint n) (hx : InBox x B)
    (hsmooth : ∃ j, eval x (pderiv j f) ≠ 0) :
    ∃ P : Finset ℕ, P ⊆ congruencePrimeWindow L ∧
      Real.exp L ≤ ∏ p ∈ P, ↑p ∧
      ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p))
        (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := hsmooth
  let D := eval x (pderiv j f)
  have hD := hj
  have hbound :=
    ((show Real.log |↑((eval x) ((pderiv j) f))| ≤
         (↑n + (1 : ℝ)) * Real.log (↑(totalDegree f) + (1 : ℝ)) + Real.log H + ↑(totalDegree f) * Real.log B from (by
       have hpos : 0 < |(eval x (pderiv j f) : ℝ)| :=
         abs_pos.mpr (by exact_mod_cast hj)
       have hdpos : 0 < (f.totalDegree : ℝ) + 1 := by positivity
       have hH0 : 0 < H := by linarith
       have hB0 : 0 < B := by linarith
       have hlog := Real.log_le_log hpos
         ((show |↑((eval x) ((pderiv j) f))| ≤ (↑(totalDegree f) + (1 : ℝ)) ^ (n + (1 : ℕ)) * H * B ^ totalDegree f from (by
            let inline_hH : (0 : ℝ) ≤ H := LT.lt.le hH0
            have hb := polynomial_eval₂_box_bound (pderiv j f)
              ((↑f.totalDegree + 1) * H) B (by positivity) hB
              ((show ∀ (e : Fin n →₀ ℕ), |↑(((pderiv j) f).coeff e)| ≤ (↑(totalDegree f) + (1 : ℝ)) * H from (by
                 intro e
                 classical
                 rw [coeff_pderiv]
                 by_cases hz : f.coeff (e + Finsupp.single j 1) = 0
                 · simp only [hz, zero_mul, Int.cast_zero, abs_zero]
                   positivity
                 · have he := by
                     have h := ((degreeOf_le_iff).mp (degreeOf_le_totalDegree f j))
                       (e + Finsupp.single j 1) (mem_support_iff.mpr hz)
                     simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using h
                   push_cast
                   rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (e j : ℝ) + 1)]
                   have heR : (e j : ℝ) + 1 ≤ ↑f.totalDegree + 1 := by
                     exact_mod_cast (by omega : e j + 1 ≤ f.totalDegree + 1)
                   calc
                     _ ≤ H * ((e j : ℝ) + 1) :=
                       mul_le_mul_of_nonneg_right (hcoeff _) (by positivity)
                     _ ≤ H * (↑f.totalDegree + 1) :=
                       mul_le_mul_of_nonneg_left heR inline_hH
                     _ = _ := by ring)))
              (fun i => (x i : ℝ)) hx
            have heval := by
              simpa only [eval₂_id, RingHom.comp_id, Function.comp_def, Int.coe_castRingHom] using
                eval₂_comp_left (Int.castRingHom ℝ) (RingHom.id ℤ) x (pderiv j f)
            rw [← heval, Fintype.card_fin] at hb
            have hdeg := (show ((pderiv j) f).totalDegree ≤ totalDegree f from (by
                           rw [← rational_map_totalDegree (pderiv j f), ← pderiv_map]
                           exact (pderiv_totalDegree_le (CCDN.rationalPolynomial f) j).trans
                             (by rw [rational_map_totalDegree]; omega)))
            calc
              _ ≤ (((pderiv j f).totalDegree : ℝ) + 1) ^ n *
                  ((↑f.totalDegree + 1) * H) * B ^ (pderiv j f).totalDegree := hb
              _ ≤ (↑f.totalDegree + 1) ^ n *
                  ((↑f.totalDegree + 1) * H) * B ^ f.totalDegree := by
                gcongr
              _ = _ := by rw [pow_succ]; ring)))
       rw [Real.log_mul (mul_pos (pow_pos hdpos _) hH0).ne' (pow_pos hB0 _).ne',
         Real.log_mul (pow_pos hdpos _).ne' hH0.ne', Real.log_pow, Real.log_pow] at hlog
       simpa only [Nat.cast_add, Nat.cast_one] using hlog))).trans hheight
  let P := (congruencePrimeWindow L).filter (fun p : ℕ => ¬ ↑p ∣ D)
  refine ⟨P, filter_subset _ _, congruencePrimeWindow_avoiding_product hL hD hbound, ?_⟩
  intro p hp
  refine ⟨j, ?_⟩
  have hnd := (mem_filter.mp hp).2
  have he : eval (fun i => (x i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) = (D : ZMod p) := by
    rw [pderiv_map]
    exact (map_eval (Int.castRingHom (ZMod p)) x (pderiv j f)).symm
  rw [he]
  exact fun h => hnd ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp h)

end CCDN
