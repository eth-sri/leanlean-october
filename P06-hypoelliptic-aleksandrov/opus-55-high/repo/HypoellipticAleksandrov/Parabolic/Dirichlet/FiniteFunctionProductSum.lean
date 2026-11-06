module

public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite sums over dependent function spaces

This file separates one coordinate in a weighted product summed over a finite dependent
function space.
-/

@[expose] public section

open scoped BigOperators


/-- A weighted product over a finite dependent function space factors coordinatewise. -/
theorem Fintype.sum_apply_mul_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {R : Type*} [CommSemiring R]
    (i : ι) (A : κ i → R) (w : ∀ j, κ j → R) :
    (∑ k : ∀ j, κ j, A (k i) * ∏ j : ι, w j (k j)) =
      (∑ a : κ i, A a * w i a) *
        ∏ j ∈ (Finset.univ.erase i), ∑ a : κ j, w j a := by
  let v  := fun j a =>
    if h : j = i then A (h ▸ a) * w j a else w j a
  have hvprod (k : ∀ j, κ j) :
      (∏ j, v j (k j)) = A (k i) * ∏ j, w j (k j) := by
    have hverase :
        (∏ j ∈ Finset.univ.erase i, v j (k j)) =
          ∏ j ∈ Finset.univ.erase i, w j (k j) := by
      apply Finset.prod_congr rfl
      grind
    rw [← Finset.mul_prod_erase Finset.univ (fun j => w j _) (Finset.mem_univ i), ← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)]
    grind
  have hvsum :
      (∏ j, ∑ a, v j a) =
        (∑ a : κ i, A a * w i a) *
          ∏ j ∈ (Finset.univ.erase i), ∑ a : κ j, w j a := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [v]
    congr 1
    apply Finset.prod_congr rfl
    simp_all
  rw [← hvsum, Fintype.prod_sum]
  simp_all
