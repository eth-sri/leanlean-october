/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-! Frobenius noncancellation from injectivity of finite coefficient jets.
These are statements about power series in prime-power characteristic. -/

@[expose] public section
namespace CCDN
noncomputable section
open PowerSeries

/-- Independent jets of length p^r prevent any nontrivial relation with
p^r-th-power power-series coefficients. -/
theorem powerSeries_frobenius_relation_trivial {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (p r : ℕ) [Fact p.Prime] [CharP K p]
    (f : ι → PowerSeries K)
    (hjet : ∀ a : ι → K, (∀ n < p ^ r, PowerSeries.coeff n (∑ i, a i • f i) = 0) → ∀ i, a i = 0)
    (g : ι → PowerSeries K) (hrel : ∑ i, f i * (g i) ^ (p ^ r) = 0) : ∀ i, g i = 0 := by
  classical
  by_contra! hn
  let : CharP (PowerSeries K) p :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective p
  let S := Finset.univ.filter (fun i => g i ≠ 0)
  have hS : S.Nonempty := by obtain ⟨i, hi⟩ := hn; exact ⟨i, by simp [S, hi]⟩
  obtain ⟨j, hj, hmin⟩ := S.exists_min_image (fun i => (g i).order.toNat) hS
  have hj0 : g j ≠ 0 := (Finset.mem_filter.mp hj).2
  let m := (g j).order.toNat
  have hdiv (i : ι) : PowerSeries.X ^ m ∣ g i := by
    by_cases hi : g i = 0
    · simp [hi]
    · exact (pow_dvd_pow PowerSeries.X (hmin i (by simp [S, hi]))).trans
        (PowerSeries.X_pow_order_dvd (φ := g i))
  choose h hh using hdiv
  have hc := PowerSeries.coeff_order hj0
  change PowerSeries.coeff m (g j) ≠ 0 at hc
  rw [hh j] at hc
  have hjc : (h j).constantCoeff ≠ 0 := by
    simpa only [PowerSeries.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] using hc
  have hfactor : (∑ i, f i * (g i) ^ (p ^ r)) =
      (PowerSeries.X : PowerSeries K) ^ (m * (p ^ r)) * ∑ i, f i * (h i) ^ (p ^ r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hh i, mul_pow, ← pow_mul]; ring
  rw [hfactor] at hrel
  have hz := (mul_eq_zero.mp hrel).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)
  have hdiff : PowerSeries.X ^ (p ^ r) ∣
      (∑ i, f i * (h i) ^ (p ^ r)) - ∑ i, ((h i).constantCoeff ^ (p ^ r)) • f i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ => ?_
    have hcong : PowerSeries.X ^ (p ^ r) ∣ (h i) ^ (p ^ r) - PowerSeries.C ((h i).constantCoeff ^ (p ^ r)) := by
      have ht := pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr (by simp) :
        (PowerSeries.X : PowerSeries K) ∣ h i - PowerSeries.C (h i).constantCoeff) (p ^ r)
      rwa [sub_pow_char_pow, ← map_pow] at ht
    convert dvd_mul_of_dvd_right hcong (f i) using 1
    rw [Algebra.smul_def, PowerSeries.algebraMap_eq]; ring
  rw [hz, zero_sub] at hdiff
  exact hjc (eq_zero_of_pow_eq_zero (hjet (fun i => (h i).constantCoeff ^ (p ^ r))
    (PowerSeries.X_pow_dvd_iff.mp (dvd_neg.mp hdiff)) j))

end
end CCDN
