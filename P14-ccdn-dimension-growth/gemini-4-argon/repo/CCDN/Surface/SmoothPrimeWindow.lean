/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- If `x` is an integer point of the box at which some partial derivative of `f` is nonzero,
and `L` dominates the logarithmic size of such a derivative, then the prime window of
logarithmic size `L` contains a set of primes with product at least `exp L` modulo each of
which `x` is a smooth point of `f`. -/
theorem exists_smooth_prime_window_subset {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) {H B L : ℝ}
    (hH : 1 ≤ H) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hcoeff : CoefficientHeightLE f H)
    (hheight : (n + 1 : ℝ) * Real.log ((f.totalDegree : ℝ) + 1) +
      Real.log H + f.totalDegree * Real.log B ≤ L)
    (x : IntPoint n) (hx : InBox x B)
    (hsmooth : ∃ j, eval x (pderiv j f) ≠ 0) :
    ∃ P : Finset ℕ, P ⊆ congruencePrimeWindow L ∧
      Real.exp L ≤ ∏ p ∈ P, (p : ℝ) ∧
      ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p))
        (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := hsmooth
  let D := eval x (pderiv j f)
  have hdpos : (0 : ℝ) < (f.totalDegree : ℝ) + 1 := by positivity
  have hH0 : 0 < H := by linarith
  have hB0 : 0 < B := by linarith
  have hpc (e : Fin n →₀ ℕ) : |((pderiv j f).coeff e : ℝ)| ≤ ((f.totalDegree : ℝ) + 1) * H := by
    rw [coeff_pderiv]
    by_cases hz : f.coeff (e + Finsupp.single j 1) = 0
    · simp only [hz, zero_mul, Int.cast_zero, abs_zero]; positivity
    · have he : e j + 1 ≤ f.totalDegree := by
        simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using
          ((degreeOf_le_iff).mp (degreeOf_le_totalDegree f j))
            (e + Finsupp.single j 1) (mem_support_iff.mpr hz)
      have heR : (e j : ℝ) + 1 ≤ f.totalDegree := mod_cast he
      push_cast
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e j : ℝ) + 1)]
      exact (mul_le_mul (hcoeff _) (by linarith) (by positivity) hH0.le).trans_eq (mul_comm _ _)
  have hb := polynomial_eval₂_box_bound (pderiv j f)
    (((f.totalDegree : ℝ) + 1) * H) B (by positivity) hB hpc (fun i => (x i : ℝ)) hx
  have heval : (D : ℝ) = eval₂ (Int.castRingHom ℝ) (fun i => (x i : ℝ)) (pderiv j f) := by
    simpa only [D, eval₂_id, RingHom.comp_id, Function.comp_def, Int.coe_castRingHom] using
      eval₂_comp_left (Int.castRingHom ℝ) (RingHom.id ℤ) x (pderiv j f)
  rw [← heval, Fintype.card_fin] at hb
  have hdeg : (pderiv j f).totalDegree ≤ f.totalDegree := by
    rw [← rational_map_totalDegree (pderiv j f), ← pderiv_map]
    exact (pderiv_totalDegree_le (map (Int.castRingHom ℚ) f) j).trans
      (by rw [rational_map_totalDegree]; omega)
  have hdegR : ((pderiv j f).totalDegree : ℝ) ≤ f.totalDegree := mod_cast hdeg
  have hD_le : |(D : ℝ)| ≤ ((f.totalDegree : ℝ) + 1) ^ (n + 1) * H * B ^ f.totalDegree := by
    calc |(D : ℝ)| ≤ (((pderiv j f).totalDegree : ℝ) + 1) ^ n *
          (((f.totalDegree : ℝ) + 1) * H) * B ^ (pderiv j f).totalDegree := hb
      _ ≤ ((f.totalDegree : ℝ) + 1) ^ n * (((f.totalDegree : ℝ) + 1) * H) * B ^ f.totalDegree := by
        gcongr
      _ = _ := by rw [pow_succ]; ring
  have hlog := Real.log_le_log (abs_pos.mpr (mod_cast hj)) hD_le
  rw [Real.log_mul (mul_pos (pow_pos hdpos _) hH0).ne' (pow_pos hB0 _).ne',
    Real.log_mul (pow_pos hdpos _).ne' hH0.ne', Real.log_pow, Real.log_pow] at hlog
  have hbound : Real.log |(D : ℝ)| ≤ L := by push_cast at hlog; linarith
  refine ⟨(congruencePrimeWindow L).filter fun p : ℕ => ¬ (p : ℤ) ∣ D,
    filter_subset _ _, congruencePrimeWindow_avoiding_product hL hj hbound, fun p hp => ⟨j, ?_⟩⟩
  erw [pderiv_map, ← map_eval (Int.castRingHom (ZMod p)) x (pderiv j f)]
  exact fun h => (mem_filter.mp hp).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp h)

end
end CCDN
