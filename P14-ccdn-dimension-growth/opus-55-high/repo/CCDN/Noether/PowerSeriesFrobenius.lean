/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-! Frobenius noncancellation from injectivity of finite coefficient jets.
These are statements about power series in prime-power characteristic. -/

namespace CCDN
section
open PowerSeries

/-- Independent jets of length p^r prevent any nontrivial relation with
p^r-th-power power-series coefficients. -/
theorem powerSeries_frobenius_relation_trivial {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (p r : ℕ) [Fact p.Prime] [CharP K p]
    (f : ι → PowerSeries K)
    (hjet : ∀ a : ι → K, (∀ n < p ^ r, PowerSeries.coeff n (∑ i, a i • f i) = 0) → ∀ i, a i = 0)
    (g : ι → PowerSeries K) (hrel : ∑ i, f i * (g i) ^ (p ^ r) = 0) : ∀ i, g i = 0 := by
  by_contra! hn
  obtain ⟨m, h, hh, j, hj⟩ : ∃ (m : ℕ) (h : ι → PowerSeries K), (∀ i, g i = PowerSeries.X ^ m * h i) ∧
      ∃ i, (h i).constantCoeff ≠ 0 := by
    classical
    let S := Finset.univ.filter (fun i => g i ≠ 0)
    have hS : S.Nonempty := by obtain ⟨i, hi⟩ := hn; exact ⟨i, by grind⟩
    obtain ⟨j, hj, hmin⟩ := S.exists_min_image (fun i => (g i).order.toNat) hS
    have hj0 := (Finset.mem_filter.mp hj).2
    let m := (g j).order.toNat
    have hdiv (i : ι) : PowerSeries.X ^ m ∣ g i := by
      by_cases hi : g i = 0
      · simp_all
      · have hle := hmin i (by simp [S, hi])
        exact (pow_dvd_pow PowerSeries.X hle).trans (PowerSeries.X_pow_order_dvd)
    choose h hh using hdiv
    refine ⟨m, h, hh, j, ?_⟩
    have hc := PowerSeries.coeff_order hj0
    change PowerSeries.coeff m (g j) ≠ 0 at hc
    rw [hh j] at hc
    simpa [PowerSeries.coeff_X_pow_mul',
      le_refl, ite_true, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply] using hc
  have hfactor : (∑ i, f i * (g i) ^ (p ^ r)) =
      (PowerSeries.X : PowerSeries K) ^ (m * (p ^ r)) * ∑ i, f i * (h i) ^ (p ^ r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hh i, mul_pow, ← pow_mul]
    ring
  have hX : (PowerSeries.X : PowerSeries K) ^ (m * (p ^ r)) ≠ 0 :=
    pow_ne_zero _ PowerSeries.X_ne_zero
  rw [hfactor] at hrel
  have hz := (mul_eq_zero.mp hrel).resolve_left hX
  exact hj ((show ∀ i, (h i).constantCoeff = 0 by
      have hdiff : PowerSeries.X ^ (p ^ r) ∣
          (∑ i, f i * (h i) ^ (p ^ r)) - ∑ i, ((h i).constantCoeff ^ (p ^ r)) • f i := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.dvd_sum
        intro i _
        have hh := dvd_mul_of_dvd_right (show PowerSeries.X ^ (p ^ r) ∣ (h i) ^ (p ^ r) - PowerSeries.C ((h i).constantCoeff ^ (p ^ r)) by
            let : CharP (PowerSeries K) p :=
              charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective p
            have hh : PowerSeries.X ∣ (h i) - PowerSeries.C (h i).constantCoeff :=
              PowerSeries.X_dvd_iff.mpr (by simp)
            have ht := pow_dvd_pow_of_dvd hh (p ^ r)
            rw [sub_pow_char_pow, ← map_pow] at ht
            exact ht) (f i)
        convert hh using 1
        rw [Algebra.smul_def, PowerSeries.algebraMap_eq]
        ring
      rw [hz, zero_sub] at hdiff
      have hzero := hjet (fun i => (h i).constantCoeff ^ (p ^ r))
        (PowerSeries.X_pow_dvd_iff.mp (dvd_neg.mp hdiff))
      intro i
      exact (eq_zero_of_pow_eq_zero (hzero i))) j)

