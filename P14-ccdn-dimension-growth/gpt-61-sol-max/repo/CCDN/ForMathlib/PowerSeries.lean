/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Linear independence of power series with distinct orders

## Main results

* `PowerSeries.linearIndependent_of_coeff_eq_zero_of_lt`: a family of power series whose first
  nonzero coefficients sit at distinct positions is linearly independent.
* `PowerSeries.linearIndependent_of_order_injective`: power series with distinct finite orders
  are linearly independent.
-/

public section

namespace PowerSeries


/-- Distinct finite power-series orders give linear independence. -/
theorem linearIndependent_of_order_injective
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (f : ι → PowerSeries K) (n : ι → ℕ) (hn : Function.Injective n)
    (horder : ∀ i, (f i).order = n i) : LinearIndependent K f := by
  apply (show (∀ (i : ι), ∀ j < n i, (coeff j) (f i) = (0 : K)) → (∀ (i : ι), (coeff (n i)) (f i) ≠ (0 : K)) → LinearIndependent K f from (by
          intro hzero hne
          classical
          rw [Fintype.linearIndependent_iff]
          intro a ha i
          by_contra hai
          let S := Finset.univ.filter (fun j => a j ≠ 0)
          have hS : S.Nonempty := ⟨i, by simp [S, hai]⟩
          obtain ⟨j, hj, hmin⟩ := S.exists_min_image n hS
          have haj := (Finset.mem_filter.mp hj).2
          have he := congrArg (PowerSeries.coeff (n j)) ha
          simp only [map_sum, PowerSeries.coeff_smul, smul_eq_mul, map_zero] at he
          have hsum : ∑ k, a k * PowerSeries.coeff (n j) (f k) =
              a j * PowerSeries.coeff (n j) (f j) := by
            apply Finset.sum_eq_single j
            · grind
            · simp
          rw [hsum] at he
          exact (mul_ne_zero haj (hne j)) he))
  · simp_all [PowerSeries.coeff_of_lt_order]
  · intro i
    exact (PowerSeries.order_eq_nat.mp (horder i)).1

end PowerSeries
