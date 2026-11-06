/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Analysis.PrimeCutoff
import CCDN.AuxiliaryPolynomial.ConstantLeadingBadReduction
import CCDN.Plane.FiniteFieldConstants
import CCDN.AuxiliaryPolynomial.BadPrimeCharge
import CCDN.ForMathlib.Log
import CCDN.Plane.ShearHeight

/-! The geometric bad-prime charge for arbitrary integer plane equations.
The proof combines bounded integral normalization, coefficient growth and an
integer minor witness; reducibility is tested over the residue field's
algebraic closure. -/

namespace CCDN
section
open Polynomial Real

section
variable (d : ℕ)

/-- The normalization cost contributes an absolute constant at the d² scale. -/
lemma normalized_shear_scaled_log_height (hd : 1 ≤ d)
    (H : ℝ) (hH : 1 ≤ H) :
    1 + 2 * Real.log (((d : ℝ) + 1) ^ (d + 2) * H) / (d : ℝ) ^ 2 ≤
      7 * (1 + Real.log H / (d : ℝ) ^ 2) := by
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hlog := Real.log_nonneg hH
  have hdlog := Real.log_add_one_le_self (Nat.cast_nonneg d)
  have hcost : ((d : ℝ) + 2) * Real.log ((d : ℝ) + 1) ≤ 3 * (d : ℝ) ^ 2 := by
    nlinarith
  rw [Real.log_mul (by positivity : ((d : ℝ) + 1) ^ (d + 2) ≠ 0) (by linarith : H ≠ 0),
    Real.log_pow]
  push_cast
  apply (le_of_mul_le_mul_right ?_ (show 0 < (d : ℝ) ^ 2 by positivity))
  field_simp
  nlinarith

end

variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] (d : ℕ) (hd : 1 ≤ d) (f : ℤ[X][X]) (hdeg : bivariateTotalDegree f = d) (hir : Irreducible (bivariateMap (Int.castRingHom F) f)) (H : ℝ) (hH : 1 ≤ H) (hcoeff : BivariateCoefficientBound f H)
include hd hdeg hir hH hcoeff

/-- Every absolutely irreducible integer plane equation has a coefficient-
controlled positive integer detecting all geometric bad primes above d. -/
theorem exists_plane_bad_prime_witness
    :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (189 * (d : ℝ) ^ 4) * (1 + Real.log H / (d : ℝ) ^ 2) ∧
      ∀ p : ℕ, d < p → BivariateBadReduction f d p → (p : ℤ) ∣ D := by
  obtain ⟨a, ha, hn, ht⟩ : ∃ a : ℕ, a ≤ bivariateTotalDegree f ∧
      (bivariateShear ℤ (a : ℤ) f).natDegree = bivariateTotalDegree f ∧
      bivariateTotalDegree (bivariateShear ℤ a f) = bivariateTotalDegree f := by
    obtain ⟨a, ha, he⟩ : ∃ a : ℕ, a ≤ bivariateTotalDegree f ∧
        (leadingDirectionPolynomial f (bivariateTotalDegree f)).eval (a : ℤ) ≠ 0 := by
      let d := bivariateTotalDegree f
      let q := leadingDirectionPolynomial f d
      by_contra! hn
      apply leadingDirectionPolynomial_ne_zero f (by aesop)
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (ι := Fin (d + 1))
        (f := fun i => (i.val : ℤ)) q
      · intro i j h
        grind
      · grind
      · have h := leadingDirectionPolynomial_natDegree_le f d
        simpa using Nat.lt_succ_of_le h
    refine ⟨a, ha, ?_, bivariateShear_totalDegree _ _⟩
    have hc : ((bivariateShear ℤ a f).coeff (bivariateTotalDegree f)).coeff 0 ≠ 0 := by
      rwa [bivariateShear_axis_coeff]
    have hp : (bivariateShear ℤ a f).coeff (bivariateTotalDegree f) ≠ 0 := by aesop
    have hlo := le_natDegree_of_ne_zero hp
    have hhi := bivariate_natDegree_le_totalDegree (bivariateShear ℤ (a : ℤ) f)
    rw [bivariateShear_totalDegree] at hhi
    omega
  rw [hdeg] at ha hn ht
  let g := bivariateShear ℤ (a : ℤ) f
  let H' := ((d : ℝ) + 1) ^ (d + 2) * H
  have hH' : 1 ≤ ((d : ℝ) + 1) ^ (d + 2) * H := by
    have hp : 1 ≤ ((d : ℝ) + 1) ^ (d + 2) :=
      one_le_pow₀ (by grind)
    nlinarith
  have hgcoeff : BivariateCoefficientBound (bivariateShear ℤ (a : ℤ) f) (((d : ℝ) + 1) ^ (d + 2) * H) := by
    apply bivariateCoefficientBound_mono (show BivariateCoefficientBound (bivariateShear ℤ (a : ℤ) f)
          (((d : ℝ) + 1) ^ 2 * H * (1 + |((a : ℤ) : ℝ)|) ^ d) by
        have he := bivariateGridPolynomial_reconstruct (d + 1) f (inBivariateGrid_of_totalDegree_lt _ _ (by omega))
        change (∑ k : BivariateGrid (d + 1),
          monomial k.1.val (monomial k.2.val ((f.coeff k.1.val).coeff k.2.val))) = f at he
        rw [← he, map_sum]
        have hb : ∀ k : BivariateGrid (d + 1),
            BivariateCoefficientBound
              (bivariateShear ℤ (a : ℤ) (monomial k.1.val (monomial k.2.val ((f.coeff k.1.val).coeff k.2.val))))
              (H * (1 + |((a : ℤ) : ℝ)|) ^ d) := by
          intro k
          apply bivariateCoefficientBound_mono
            (show BivariateCoefficientBound (bivariateShear ℤ (a : ℤ) (monomial k.1.val (monomial k.2.val _)))
                  (|(_ : ℝ)| * (1 + |((a : ℤ) : ℝ)|) ^ k.2.val) by
                rw [bivariateShear_monomial]
                exact bivariateCoefficientBound_monomial_mul (by positivity)
                  (bivariateCoefficientBound_shear_linear_pow (a : ℤ) k.2.val) _ k.1.val 0)
          exact mul_le_mul (hcoeff _ _) (pow_le_pow_right₀ (by linarith [abs_nonneg ((a : ℤ) : ℝ)]) (by omega))
            (by positivity) (by linarith)
        have hh := bivariateCoefficientBound_sum _ _ hb
        convert hh using 1
        simp
        ring)
    simp
    have haR : (a : ℝ) ≤ d := mod_cast ha
    calc
      _ ≤ ((d : ℝ) + 1) ^ 2 * H * ((d : ℝ) + 1) ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + a by positivity)
          (show (1 : ℝ) + a ≤ d + 1 by linarith) d) (by positivity)
      _ = _ := by grind
  have hgir : Irreducible (bivariateMap (Int.castRingHom F) g) := by
    rwa [bivariateShear_map, bivariateShear_irreducible_iff]
  obtain ⟨D, hD, hheight, hdiv⟩ :=
    exists_full_outer_bad_prime_witness d hd g hn ht.le hgir H' hH' hgcoeff
  refine ⟨D, hD, ?_, ?_⟩
  · have hs := normalized_shear_scaled_log_height d hd H hH
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 27 * (d : ℝ) ^ 4 by positivity)
    nlinarith
  · intro p hp hbad
    apply hdiv p hp
    exact (show BivariateBadReduction (bivariateShear ℤ (a : ℤ) f) d p ↔ BivariateBadReduction f d p by
        constructor
        · rintro ⟨hp, hbad⟩
          refine ⟨hp, ?_⟩
          simp_all [bivariateShear_map, bivariateShear_totalDegree, bivariateShear_irreducible_iff]
        · rintro ⟨hp, hbad⟩
          refine ⟨hp, ?_⟩
          simp_all [bivariateShear_map, bivariateShear_totalDegree, bivariateShear_irreducible_iff]).mpr hbad

/-- Geometric bad primes above 27*d^4 have logarithmic charge controlled by
log(1+log(H)/d²) plus an absolute constant. -/
theorem plane_geometric_bad_prime_charge
    (P : Finset ℕ) (hbad : ∀ p ∈ P, BivariateBadReduction f d p)
    (hlo : ∀ p ∈ P, stepanovThreshold (d : ℝ) < (p : ℝ)) :
    (∑ p ∈ P, Real.log p / p) ≤
      Real.log (1 + Real.log H / (d : ℝ) ^ 2) + Real.log 7 + 2 * mertensError + 1 := by
  obtain ⟨D, hD, hheight, hdiv⟩ := exists_plane_bad_prime_witness d hd f hdeg hir H hH hcoeff
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hx : 1 ≤ 1 + Real.log H / (d : ℝ) ^ 2 :=
    le_add_of_nonneg_right (div_nonneg (Real.log_nonneg hH) (sq_nonneg _))
  have hcut : (d : ℝ) ≤ 27 * (d : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((d : ℝ) ^ 2 - 1)]
  have h := bad_prime_charge_of_height (L := 27 * (d : ℝ) ^ 4)
    (H := 7 * (1 + Real.log H / (d : ℝ) ^ 2)) P hD
    (fun p hp => (hbad p hp).choose)
    (fun p hp => hdiv p (mod_cast hcut.trans_lt (hlo p hp)) (hbad p hp))
    (by linarith) (by linarith) hlo (by grind)
  rw [Real.log_mul (by norm_num : (7 : ℝ) ≠ 0)
    (by grind)] at h
  linarith

