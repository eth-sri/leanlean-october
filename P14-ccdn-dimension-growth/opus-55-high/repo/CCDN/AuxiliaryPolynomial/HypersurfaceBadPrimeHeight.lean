/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Analysis.PrimeCutoff
import CCDN.AuxiliaryPolynomial.DegreeBound
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimes
import CCDN.Plane.IntegerPlaneLogHeight
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.AuxiliaryPolynomial.BadPrimeCharge
import CCDN.AuxiliaryPolynomial.UniversalPlaneBadReduction
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Determinant.ClosedFormMinorCharge

/-!
The geometric bad-prime charge in arbitrary dimension is controlled by
coefficient height, via an explicit integer witness with bounded height.

A nonzero bad-prime witness obtained by evaluating the universal
plane polynomial on a bounded integer grid.

Explicit height estimates for the evaluated universal bad-prime witness.
-/

namespace CCDN
open MvPolynomial

variable {σ : Type*}

end CCDN

namespace CCDN
open MvPolynomial

lemma bad_prime_dvd_universalPlaneBadWitness_eval {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℤ) (hpos : 0 < f.totalDegree)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (v : PlaneParameters σ → ℤ) (p : ℕ)
    (hp : f.totalDegree < p) (hbad : HypersurfaceBadReduction f p) :
    (p : ℤ) ∣ eval v (universalPlaneBadWitness f rows cols) := by
  obtain ⟨hpprime, hbad⟩ := hbad
  let : Fact p.Prime := ⟨hpprime⟩
  rw [eval_eq']
  apply Finset.dvd_sum
  intro e _
  exact dvd_mul_of_dvd_left
    (bad_prime_dvd_universalPlaneBadWitness_coeff f hpos rows cols p hp hbad e) _

variable {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ] (f : MvPolynomial (Option σ) ℤ) (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f)) (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
include hf hpos hH hcoeff

/-- An effective positive integer detecting every bad prime above the degree. -/
theorem exists_hypersurface_bad_prime_height_witness
    :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (27 * (f.totalDegree : ℝ) ^ 4) *
        (hypersurfaceHeightConstant (Fintype.card (Option σ)) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) ∧
      ∀ p : ℕ, f.totalDegree < p → HypersurfaceBadReduction f p → (p : ℤ) ∣ D := by
  obtain ⟨rows, cols, hw, hd⟩ := exists_integer_universalPlane_badWitness f hf hpos
  obtain ⟨v, hv, hw⟩ := exists_integer_grid_eval_ne_zero _ hw _ hd
  let S := integerPlaneHeight (Fintype.card (Option σ)) f.totalDegree H
    (2 * (f.totalDegree : ℝ) ^ 3)
  have hd := hpos
  have hdR : (1 : ℝ) ≤ f.totalDegree := mod_cast hd
  have hA : 1 ≤ 2 * (f.totalDegree : ℝ) ^ 3 := by bound
  have hv' (i : PlaneParameters (Option σ)) : |(v i : ℝ)| ≤ 2 * (f.totalDegree : ℝ) ^ 3 := by
    rw [abs_of_nonneg (by simp_all)]
    exact_mod_cast (hv i).2
  have hcoeffS :=
    integer_plane_section_coefficient_bound f H _ (by linarith) hA hcoeff v hv'
  refine ⟨|eval v (universalPlaneBadWitness f rows cols)|, abs_pos.mpr hw, ?_, ?_⟩
  · rw [Int.cast_abs]
    exact (show Real.log |(eval v (universalPlaneBadWitness f rows cols) : ℝ)| ≤
          Real.log S + (27 * f.totalDegree ^ 4) *
            (1 + Real.log S / (f.totalDegree : ℝ) ^ 2) by
        let g := universalPlaneSection f v
        let c := (g.coeff f.totalDegree).coeff 0
        let D := ((closedFormCoefficientMatrix f.totalDegree g).submatrix rows cols).det
        have he : eval v (universalPlaneBadWitness f rows cols) =
            ((universalPlaneSection f v).coeff f.totalDegree).coeff 0 *
              ((closedFormCoefficientMatrix f.totalDegree (universalPlaneSection f v)).submatrix
                rows cols).det := by
          rw [universalPlaneBadWitness, map_mul, closedForm_minor_map]
          congr 1
          exact (bivariateMap_coeff (eval v) (universalPlanePolynomial f) f.totalDegree 0).symm
        have hc : c ≠ 0 := fun h => hw (by grind)
        have hD : D ≠ 0 := fun h => hw (by grind)
        have ht :=
          universalPlanePolynomial_specialization_totalDegree f (eval v)
        have hb := closedForm_minor_log_height f.totalDegree (2 * f.totalDegree ^ 2 - 1)
          hd (Nat.sub_le _ _) g S (integerPlaneHeight_one_le _ _ hd H hH) hcoeffS
          ((bivariate_natDegree_le_totalDegree g).trans ht)
          (fun i => (bivariate_coefficient_natDegree_le_totalDegree g i).trans ht) rows cols hD
        have hl := Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hc)) (hcoeffS f.totalDegree 0)
        rw [he, Int.cast_mul, abs_mul, Real.log_mul
          (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hc)) (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hD))]
        exact add_le_add hl hb).trans
      (integerPlaneHeight_scaled_log_le _ _ hd H hH)
  · simpa using bad_prime_dvd_universalPlaneBadWitness_eval f hpos rows cols v

/-- The logarithmic charge bound for any finite family of bad primes.
This includes degree-dropping primes as well as geometric reducibility. -/
theorem hypersurface_bad_prime_charge
    (P : Finset ℕ) (hP : ∀ p ∈ P, HypersurfaceBadReduction f p)
    (hcut : ∀ p ∈ P, stepanovThreshold f.totalDegree < p) :
    (∑ p ∈ P, Real.log p / p) ≤
      Real.log (hypersurfaceHeightConstant (Fintype.card (Option σ)) *
        (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1 := by
  obtain ⟨D, hD, hheight, hdiv⟩ :=
    exists_hypersurface_bad_prime_height_witness f hf hpos H hH hcoeff
  have hd1 : (1 : ℝ) ≤ f.totalDegree := mod_cast hpos
  apply bad_prime_charge_of_height P hD (fun p hp => (hP p hp).choose) _ _ _ _ hheight
  · intro p hp
    apply hdiv p _ (hP p hp)
    have h1 := Nat.le_mul_self f.totalDegree
    have h3 : 27 * f.totalDegree ^ 4 < p := hcut p hp
    nlinarith
  · bound
  · exact one_le_mul_of_one_le_of_one_le (hypersurfaceHeightConstant_one_le _)
      (le_add_of_nonneg_right (div_nonneg (Real.log_nonneg hH) (sq_nonneg _)))
  · intro p hp
    exact_mod_cast hcut p hp

