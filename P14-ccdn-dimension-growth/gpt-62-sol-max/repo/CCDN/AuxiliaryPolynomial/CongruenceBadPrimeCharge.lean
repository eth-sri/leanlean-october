/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Analysis.PrimeCutoff
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimes
public import CCDN.Plane.IntegerPlaneLogHeight
import CCDN.AuxiliaryPolynomial.BadPrimeCharge
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates

/-! A single logarithmic-height witness bounds the combined charge of
geometric bad primes and prescribed congruence primes. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- Combine the logarithmic budget of the bad primes with that of the prescribed primes. -/
theorem hypersurface_and_congruence_prime_charge
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : Irreducible (map (Int.castRingHom L) f)) (hd : 0 < f.totalDegree)
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
    (bad P : Finset ℕ)
    (hbad : ∀ p ∈ bad, stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ bad ∪ P, Real.log p / p) ≤
      Real.log (1 + 27 * (f.totalDegree : ℝ) ^ 4 *
        (hypersurfaceHeightConstant (n + 1) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) +
        (∑ p ∈ P, Real.log p)) + 2 * mertensError + 1 := by
  classical
  obtain ⟨D, hD, hheight, hdiv⟩ :=
    exists_fin_hypersurface_bad_prime_height_witness f hf hd H hH hcoeff
  let A := 27 * (f.totalDegree : ℝ) ^ 4 * (hypersurfaceHeightConstant (n + 1) *
    (1 + Real.log H / (f.totalDegree : ℝ) ^ 2))
  have hprime p hp := (hbad p hp).2.choose
  have hlog : (∑ p ∈ bad, Real.log p) ≤ A :=
    (prime_divisor_log_sum_le bad hD hprime (fun p hp =>
      hdiv p ((degree_le_stepanovThreshold _).trans_lt (hbad p hp).1) (hbad p hp).2)).trans hheight
  have hsum : 0 ≤ ∑ p ∈ P, Real.log p := sum_nonneg (fun p _ => Real.log_natCast_nonneg p)
  have hA : 0 ≤ A := by
    have hC := (hypersurfaceHeightConstant_one_le (n + 1)).trans' zero_le_one
    have hlogH := Real.log_nonneg hH
    positivity
  apply bad_prime_charge_of_log_sum (bad ∪ P) (L := 1)
    (H := 1 + A + ∑ p ∈ P, Real.log p)
  · intro p hp
    exact (mem_union.mp hp).elim (hprime p) (hP p)
  · norm_num
  · linarith
  · intro p hp
    exact_mod_cast ((mem_union.mp hp).elim (hprime p) (hP p)).one_lt
  · rw [one_mul, ← sum_inter_add_sum_sdiff (bad ∪ P) P (fun p => Real.log p)] at ⊢
    rw [union_inter_cancel_right]
    have hh := sum_le_sum_of_subset_of_nonneg (s := (bad ∪ P) \ P) (t := bad)
      (f := fun p : ℕ => Real.log p) (by intro p; simp; tauto) (fun p _ _ => Real.log_natCast_nonneg p)
    linarith

end
end CCDN
