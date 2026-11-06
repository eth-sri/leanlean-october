/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.FilteredIntersection
import CCDN.ForMathlib.MvPolynomial

/-! Two finite differences of a binomial Hilbert function. This gives a
coefficient-uniform codimension-two bound for filtered coordinate spaces. -/

namespace CCDN
section

section
variable (n k d : ℕ)

lemma choose_shift_sum :
    (n + 1 + (k + d)).choose (n + 1) = (n + 1 + k).choose (n + 1) +
      ∑ i ∈ Finset.range d, (n + (k + i + 1)).choose n := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    rw [show n + 1 + (k + (d + 1)) = (n + 1 + (k + d)) + 1 by omega,
      Nat.choose_succ_succ', ih]
    rw [show n + 1 + (k + d) = n + (k + d + 1) by omega]
    omega

lemma choose_shift_bound :
    (n + 1 + (k + d)).choose (n + 1) ≤ (n + 1 + k).choose (n + 1) +
      d * (n + (k + d)).choose n := by
  rw [choose_shift_sum]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _i ∈ Finset.range d, (n + (k + d)).choose n := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.choose_le_choose n (by grind)
    _ = _ := by simp

end

/-- The second finite difference has the product-of-degrees factor and loses
two powers of the cutoff, in every ambient dimension. -/
theorem choose_double_difference_bound (n k d e : ℕ) :
    (n + 2 + (k + d + e)).choose (n + 2) + (n + 2 + k).choose (n + 2) ≤
      (n + 2 + (k + d)).choose (n + 2) + (n + 2 + (k + e)).choose (n + 2) +
        d * e * (n + (k + d + e)).choose n := by
  have h1 := choose_shift_sum (n + 1) (k + e) d
  have h2 := choose_shift_sum (n + 1) k d
  have hsum : (∑ i ∈ Finset.range d, (n + 1 + (k + e + i + 1)).choose (n + 1)) ≤
      (∑ i ∈ Finset.range d, (n + 1 + (k + i + 1)).choose (n + 1)) +
        d * e * (n + (k + d + e)).choose n := by
    calc
      _ ≤ ∑ i ∈ Finset.range d,
          ((n + 1 + (k + i + 1)).choose (n + 1) +
            e * (n + (k + d + e)).choose n) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := choose_shift_bound n (k + i + 1) e
        have hmono := Nat.choose_le_choose n
          (show n + (k + i + 1 + e) ≤ n + (k + d + e) by grind)
        have hm := Nat.mul_le_mul_left e hmono
        rw [show k + i + 1 + e = k + e + i + 1 by omega] at h hm
        omega
      _ = _ := by rw [Finset.sum_add_distrib]; simp [Nat.mul_assoc]
  rw [show k + e + d = k + d + e by omega] at h1
  rw [show n + 1 + 1 = n + 2 by omega] at h1 h2
  omega

/-- The filtered Koszul bound reduces to a codimension-two binomial count. -/
theorem filteredCoordinateSpace_codim_two_bound {K : Type*} [Field K] {n N : ℕ}
    {f g : MvPolynomial (Fin (n + 2)) K} (hf : Prime f) (hfg : ¬ f ∣ g)
    (I : Ideal (MvPolynomial (Fin (n + 2)) K)) (hIf : f ∈ I) (hIg : g ∈ I)
    (hN : f.totalDegree + g.totalDegree ≤ N) :
    Module.finrank K (filteredCoordinateSpace I N) ≤
      f.totalDegree * g.totalDegree * (n + N).choose n := by
  let φ := (Ideal.Quotient.mkₐ K I).toLinearMap
  have hker (p : MvPolynomial (Fin (n + 2)) K) (hp : p ∈ I) : filteredMultiples p N ≤ φ.ker := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := (mem_filteredMultiples p x N).mp hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact I.mul_mem_right u hp
  have h := finrank_map_add_kernel_subspace_le φ (MvPolynomial.restrictTotalDegree _ K N)
    (filteredMultiples f N ⊔ filteredMultiples g N)
    (sup_le (filteredMultiples_le_degree f (by omega))
      (filteredMultiples_le_degree g (by omega)))
    (sup_le (hker f hIf) (hker g hIg))
  have heq := filteredMultiples_sup_finrank hf hfg hN
  change Module.finrank K (filteredCoordinateSpace I N) + _ ≤ _ at h
  simp [MvPolynomial.finrank_restrictTotalDegree, Fintype.card_fin,
    ← Nat.choose_symm_add (a := n + 2)] at h heq
  have hc := choose_double_difference_bound n (N - (f.totalDegree + g.totalDegree))
    f.totalDegree g.totalDegree
  have h0 : N - (f.totalDegree + g.totalDegree) + f.totalDegree + g.totalDegree = N := by omega
  have h1 : N - (f.totalDegree + g.totalDegree) + f.totalDegree = N - g.totalDegree := by omega
  have h2 : N - (f.totalDegree + g.totalDegree) + g.totalDegree = N - f.totalDegree := by omega
  rw [h0, h1, h2] at hc
  omega

