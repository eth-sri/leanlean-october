/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Analysis.PrimeCutoff
public import CCDN.AuxiliaryPolynomial.ConstantLeadingBadReduction
public import CCDN.Plane.FiniteFieldConstants
import CCDN.AuxiliaryPolynomial.BadPrimeCharge
import CCDN.ForMathlib.Log
import CCDN.Plane.ShearHeight

/-! The geometric bad-prime charge for arbitrary integer plane equations.
The proof combines bounded integral normalization, coefficient growth and an
integer minor witness; reducibility is tested over the residue field's
algebraic closure. -/

public section
namespace CCDN
open Polynomial Real


/-- The normalization cost contributes an absolute constant at the d² scale. -/
private lemma normalized_shear_scaled_log_height (d : ℕ) (hd : 1 ≤ d)
    (H : ℝ) (hH : 1 ≤ H) :
    1 + 2 * Real.log ((↑d + 1) ^ (d + 2) * H) / ↑d ^ 2 ≤
      7 * (1 + Real.log H / ↑d ^ 2) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog := Real.log_nonneg hH
  have hdlog := Real.log_add_one_le_self (Nat.cast_nonneg  d)
  rw [Real.log_mul (by positivity : ((d : ℝ) + 1) ^ (d + 2) ≠ 0) (by linarith : H ≠ 0),
    Real.log_pow]
  push_cast
  apply (le_of_mul_le_mul_right ?_ (show 0 < (d : ℝ) ^ 2 by positivity))
  field_simp
  nlinarith

variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] (d : ℕ) (hd : 1 ≤ d) (f : ℤ[X][X]) (hdeg : bivariateTotalDegree f = d) (hir : Irreducible (bivariateMap (Int.castRingHom F) f)) (H : ℝ) (hH : 1 ≤ H) (hcoeff : BivariateCoefficientBound f H)

include hd hdeg hir hH hcoeff in
/-- Every absolutely irreducible integer plane equation has a coefficient-
controlled positive integer detecting all geometric bad primes above d. -/
theorem exists_plane_bad_prime_witness
     :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (189 * ↑d ^ 4) * (1 + Real.log H / ↑d ^ 2) ∧
      ∀ p : ℕ, d < p → BivariateBadReduction f d p → ↑p ∣ D := by
  have hf : f ≠ 0 := by
    aesop
  obtain ⟨a, ha, hn, ht⟩ := exists_bounded_full_outer_shear f hf
  rw [hdeg] at ha hn ht
  let g := bivariateShear ℤ ↑a f
  let H' := (↑d + 1) ^ (d + 2) * H
  have hH' := (show (1 : ℝ) ≤ (↑d + (1 : ℝ)) ^ (d + (2 : ℕ)) * H from (by
                have hp : 1 ≤ ((d : ℝ) + 1) ^ (d + 2) :=
                  one_le_pow₀ (by simp_all)
                nlinarith))
  have hgcoeff :=
    bivariateShear_bounded_coefficient_bound a d ha f hdeg.le H (by linarith) hcoeff
  have hgir : Irreducible (bivariateMap (Int.castRingHom F) g) := by
    grind [bivariateShear_map, bivariateShear_irreducible_iff]
  obtain ⟨D, hD, hheight, hdiv⟩ :=
    exists_full_outer_bad_prime_witness d hd g hn ht.le hgir H' hH' hgcoeff
  refine ⟨D, hD, ?_, ?_⟩
  · have hs := normalized_shear_scaled_log_height d hd H hH
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 27 * ↑d ^ 4 by positivity)
    nlinarith
  · grind [bivariateBadReduction_shear_iff]

include hd hdeg hir hH hcoeff in
/-- Geometric bad primes above 27*d^4 have logarithmic charge controlled by
log(1+log(H)/d²) plus an absolute constant. -/
theorem plane_geometric_bad_prime_charge
    
    (P : Finset ℕ) (hbad : ∀ p ∈ P, BivariateBadReduction f d p)
    (hlo : ∀ p ∈ P, stepanovThreshold ↑d < (p : ℝ)) :
    (∑ p ∈ P, Real.log p / p) ≤
      Real.log (1 + Real.log H / ↑d ^ 2) + Real.log 7 + 2 * mertensError + 1 := by
  obtain ⟨D, hD, hheight, hdiv⟩ := exists_plane_bad_prime_witness d hd f hdeg hir H hH hcoeff
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : 1 ≤ 1 + Real.log H / ↑d ^ 2 :=
    le_add_of_nonneg_right (div_nonneg (Real.log_nonneg hH) (sq_nonneg _))
  have hcut : ↑d ≤ 27 * (d : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((d : ℝ) ^ 2 - 1)]
  have h := bad_prime_charge_of_height (D := D) (L := 27 * ↑d ^ 4)
    (H := 7 * (1 + Real.log H / ↑d ^ 2)) P hD
    (fun p hp => (hbad p hp).choose)
    (fun p hp => hdiv p (by exact_mod_cast hcut.trans_lt (hlo p hp)) (hbad p hp))
    (by linarith) (by linarith) hlo (by nlinarith [hheight])
  rw [Real.log_mul (by norm_num : (7 : ℝ) ≠ 0)
    (by linarith : 1 + Real.log H / ↑d ^ 2 ≠ 0)] at h
  linarith

end CCDN
