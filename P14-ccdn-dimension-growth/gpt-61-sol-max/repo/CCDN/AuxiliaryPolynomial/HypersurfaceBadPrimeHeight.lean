/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateCoefficientMatrix
import Mathlib

public import CCDN.Analysis.PrimeCutoff
public import CCDN.AuxiliaryPolynomial.DegreeBound
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimes
public import CCDN.Plane.IntegerPlaneLogHeight
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

public section
namespace CCDN
open MvPolynomial



end CCDN

namespace CCDN
open MvPolynomial


end CCDN

namespace CCDN
open MvPolynomial

variable {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ] (f : MvPolynomial (Option σ) ℤ) (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f)) (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)

include hf hpos hH hcoeff in
/-- An effective positive integer detecting every bad prime above the degree. -/
theorem exists_hypersurface_bad_prime_height_witness
     :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (27 * ↑f.totalDegree ^ 4) *
        (hypersurfaceHeightConstant (Fintype.card (Option σ)) *
          (1 + Real.log H / ↑f.totalDegree ^ 2)) ∧
      ∀ p : ℕ, f.totalDegree < p → HypersurfaceBadReduction f p → ↑p ∣ D := by
  obtain ⟨rows, cols, v, hv, hw, hdiv⟩ := (show ∃ rows cols v,
                                              (∀ (i : PlaneParameters (Option σ)), (0 : ℤ) ≤ v i ∧ v i ≤ ↑((2 : ℕ) * f.totalDegree ^ (3 : ℕ))) ∧
                                                (eval v) (universalPlaneBadWitness f rows cols) ≠ (0 : ℤ) ∧
                                                  ∀ (p : ℕ), f.totalDegree < p → HypersurfaceBadReduction f p → ↑p ∣ (eval v) (universalPlaneBadWitness f rows cols) from (by
                                            obtain ⟨rows, cols, hw, hd⟩ := exists_integer_universalPlane_badWitness f hf hpos
                                            obtain ⟨v, hv, he⟩ := exists_integer_grid_eval_ne_zero _ hw _ hd
                                            exact ⟨rows, cols, v, hv, he,
                                              ((show ∀ (p : ℕ), f.totalDegree < p → HypersurfaceBadReduction f p → ↑p ∣ (eval v) (universalPlaneBadWitness f rows cols) from (by
                                                 intro p hp hbad
                                                 classical
                                                 obtain ⟨hpprime, hbad⟩ := hbad
                                                 let : Fact p.Prime := ⟨hpprime⟩
                                                 apply Finset.dvd_sum
                                                 intro e _
                                                 solve_by_elim [dvd_mul_of_dvd_left, bad_prime_dvd_universalPlaneBadWitness_coeff])))⟩))
  let S := integerPlaneHeight (Fintype.card (Option σ)) f.totalDegree H
    (2 * ↑f.totalDegree ^ 3)
  have hd := hpos
  have hdR : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
  have hA : 1 ≤ 2 * (f.totalDegree : ℝ) ^ 3 := by grind [one_le_pow₀]
  have hv' (i : PlaneParameters (Option σ)) : |(v i : ℝ)| ≤ 2 * ↑f.totalDegree ^ 3 := by
    rw [abs_of_nonneg (by exact_mod_cast (hv i).1)]
    exact_mod_cast (hv i).2
  have hS : 1 ≤ S := integerPlaneHeight_one_le _ _ hd H hH
  have hcoeffS :=
    integer_plane_section_coefficient_bound f H _ (by linarith) hA hcoeff v hv'
  refine ⟨|eval v (universalPlaneBadWitness f rows cols)|, abs_pos.mpr hw, ?_, ?_⟩
  · rw [Int.cast_abs]
    exact ((show Real.log |↑((eval v) (universalPlaneBadWitness f rows cols))| ≤
               Real.log S + (27 : ℝ) * ↑f.totalDegree ^ (4 : ℕ) * ((1 : ℝ) + Real.log S / ↑f.totalDegree ^ (2 : ℕ)) from (by
             let g := universalPlaneSection f v
             let c := (g.coeff f.totalDegree).coeff 0
             let D := ((closedFormCoefficientMatrix f.totalDegree g).submatrix rows cols).det
             have he : eval v (universalPlaneBadWitness f rows cols) = c * D :=
               (show (eval v) (universalPlaneBadWitness f rows cols) =
                   ((universalPlaneSection f v).coeff f.totalDegree).coeff (0 : ℕ) *
                     ((closedFormCoefficientMatrix f.totalDegree (universalPlaneSection f v)).submatrix rows cols).det from (by
                 rw [universalPlaneBadWitness, map_mul, closedForm_minor_map]
                 congr 1
                 exact (bivariateMap_coeff (eval v) (universalPlanePolynomial f) f.totalDegree 0).symm))
             have hc : c ≠ 0 := fun h => hw (by rw [he, h, zero_mul])
             have hD : D ≠ 0 := fun h => hw (by rw [he, h, mul_zero])
             have ht :=
               universalPlanePolynomial_specialization_totalDegree f (eval v)
             have hb := closedForm_minor_log_height f.totalDegree (2 * f.totalDegree ^ 2 - 1)
               hd (Nat.sub_le _ _) g S hS hcoeffS
               ((bivariate_natDegree_le_totalDegree g).trans ht)
               (fun i => (bivariate_coefficient_natDegree_le_totalDegree g i).trans ht) rows cols hD
             have hl := Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hc)) (hcoeffS f.totalDegree 0)
             rw [he, Int.cast_mul, abs_mul, Real.log_mul
               (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hc)) (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hD))]
             exact add_le_add hl hb))).trans
      (integerPlaneHeight_scaled_log_le _ _ hd H hH)
  · simp_all

include hf hpos hH hcoeff in
/-- The logarithmic charge bound for any finite family of bad primes.
This includes degree-dropping primes as well as geometric reducibility. -/
theorem hypersurface_bad_prime_charge
    
    (P : Finset ℕ) (hP : ∀ p ∈ P, HypersurfaceBadReduction f p)
    (hcut : ∀ p ∈ P, stepanovThreshold f.totalDegree < p) :
    (∑ p ∈ P, Real.log p / p) ≤
      Real.log (hypersurfaceHeightConstant (Fintype.card (Option σ)) *
        (1 + Real.log H / ↑f.totalDegree ^ 2)) + 2 * mertensError + 1 := by
  obtain ⟨D, hD, hheight, hdiv⟩ :=
    exists_hypersurface_bad_prime_height_witness f hf hpos H hH hcoeff
  have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hpos
  apply bad_prime_charge_of_height P hD (fun p hp => (hP p hp).choose) _ _ _ _ hheight
  · intro p hp
    apply hdiv p _ (hP p hp)
    have h2 := Nat.le_mul_self (f.totalDegree * f.totalDegree)
    have h3 : 27 * f.totalDegree ^ 4 < p := hcut p hp
    nlinarith [h3]
  · grind [one_le_pow₀]
  · exact one_le_mul_of_one_le_of_one_le (hypersurfaceHeightConstant_one_le _)
      (le_add_of_nonneg_right (div_nonneg (Real.log_nonneg hH) (sq_nonneg _)))
  · intro p hp
    exact_mod_cast hcut p hp

end CCDN
