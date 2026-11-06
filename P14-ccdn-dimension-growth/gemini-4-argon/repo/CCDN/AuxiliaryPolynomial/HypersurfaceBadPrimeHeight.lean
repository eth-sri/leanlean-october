/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- An effective positive integer detecting every bad prime above the degree. -/
theorem exists_hypersurface_bad_prime_height_witness
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H) :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (27 * (f.totalDegree : ℝ) ^ 4) *
        (hypersurfaceHeightConstant (Fintype.card (Option σ)) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) ∧
      ∀ p : ℕ, f.totalDegree < p → HypersurfaceBadReduction f p → (p : ℤ) ∣ D := by
  classical
  obtain ⟨rows, cols, hnz, hd_w⟩ := exists_integer_universalPlane_badWitness f hf hpos
  obtain ⟨v, hv, hw⟩ := exists_integer_grid_eval_ne_zero _ hnz _ hd_w
  let S := integerPlaneHeight (Fintype.card (Option σ)) f.totalDegree H
    (2 * (f.totalDegree : ℝ) ^ 3)
  have hd : 1 ≤ f.totalDegree := hpos
  have hdR : (1 : ℝ) ≤ f.totalDegree := mod_cast hd
  have hA : 1 ≤ 2 * (f.totalDegree : ℝ) ^ 3 := by nlinarith [one_le_pow₀ hdR (n := 3)]
  have hv' (i : PlaneParameters (Option σ)) : |(v i : ℝ)| ≤ 2 * (f.totalDegree : ℝ) ^ 3 := by
    rw [abs_of_nonneg (mod_cast (hv i).1)]
    exact_mod_cast (hv i).2
  have hS : 1 ≤ S := integerPlaneHeight_one_le _ _ hd H hH
  let g := universalPlaneSection f v
  have hcoeffS : BivariateCoefficientBound g S :=
    integer_plane_section_coefficient_bound f H _ (by linarith) hA hcoeff v hv'
  let c := (g.coeff f.totalDegree).coeff 0
  let M := ((closedFormCoefficientMatrix f.totalDegree g).submatrix rows cols).det
  have he : eval v (universalPlaneBadWitness f rows cols) = c * M := by
    rw [universalPlaneBadWitness, map_mul, closedForm_minor_map]
    congr 1
    exact (bivariateMap_coeff (eval v) (universalPlanePolynomial f) f.totalDegree 0).symm
  have hc : c ≠ 0 := fun h => hw (by rw [he, h, zero_mul])
  have hM : M ≠ 0 := fun h => hw (by rw [he, h, mul_zero])
  have ht : bivariateTotalDegree g ≤ f.totalDegree :=
    universalPlanePolynomial_specialization_totalDegree f (eval v)
  have hb := closedForm_minor_log_height f.totalDegree (2 * f.totalDegree ^ 2 - 1)
    hd (Nat.sub_le _ _) g S hS hcoeffS
    ((bivariate_natDegree_le_totalDegree g).trans ht)
    (fun i => (bivariate_coefficient_natDegree_le_totalDegree g i).trans ht) rows cols hM
  have hl := Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hc)) (hcoeffS f.totalDegree 0)
  refine ⟨|eval v (universalPlaneBadWitness f rows cols)|, abs_pos.mpr hw, ?_,
    fun p hp ⟨hpprime, hbad⟩ => ?_⟩
  · rw [Int.cast_abs, he, Int.cast_mul, abs_mul, Real.log_mul
      (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hc)) (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hM))]
    exact (add_le_add hl hb).trans (integerPlaneHeight_scaled_log_le _ _ hd H hH)
  · let : Fact p.Prime := ⟨hpprime⟩
    rw [dvd_abs, eval_eq']
    exact Finset.dvd_sum fun e _ => dvd_mul_of_dvd_left
      (bad_prime_dvd_universalPlaneBadWitness_coeff f hpos rows cols p hp hbad e) _

/-- The logarithmic charge bound for any finite family of bad primes.
This includes degree-dropping primes as well as geometric reducibility. -/
theorem hypersurface_bad_prime_charge
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H)
    (P : Finset ℕ) (hP : ∀ p ∈ P, HypersurfaceBadReduction f p)
    (hcut : ∀ p ∈ P, stepanovThreshold f.totalDegree < p) :
    (∑ p ∈ P, Real.log p / p) ≤
      Real.log (hypersurfaceHeightConstant (Fintype.card (Option σ)) *
        (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1 := by
  obtain ⟨D, hD, hheight, hdiv⟩ :=
    exists_hypersurface_bad_prime_height_witness f hf hpos H hH hcoeff
  have hd1 : (1 : ℝ) ≤ f.totalDegree := mod_cast hpos
  refine bad_prime_charge_of_height P hD (fun p hp => (hP p hp).choose)
    (fun p hp => hdiv p ?_ (hP p hp)) (by nlinarith [one_le_pow₀ hd1 (n := 4)])
    (one_le_mul_of_one_le_of_one_le (hypersurfaceHeightConstant_one_le _)
      (le_add_of_nonneg_right (div_nonneg (Real.log_nonneg hH) (sq_nonneg _))))
    (fun p hp => mod_cast hcut p hp) hheight
  have h3 : 27 * f.totalDegree ^ 4 < p := hcut p hp
  nlinarith [Nat.le_mul_self f.totalDegree, Nat.le_mul_self (f.totalDegree * f.totalDegree)]

end
end CCDN
