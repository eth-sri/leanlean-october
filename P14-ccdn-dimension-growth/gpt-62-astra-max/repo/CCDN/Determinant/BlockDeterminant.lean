/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.MinorGcd

/-! Combining maximal-minor divisibility across row blocks. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix Module Finset

variable {c s N : ℕ} (A : Matrix (Fin s) (Fin N) ℤ) (label : Fin s → Fin c) (i : Fin c)

/-- The product of common divisors of the maximal minors of disjoint row blocks
is a divisor of the full determinant. Empty and rank-deficient blocks are allowed. -/
private theorem block_minor_divisors_dvd_det (n : Fin c → ℕ)
    (A : Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℤ) (d : Fin c → ℤ)
    (hd : ∀ i, ∀ j : Fin (n i) → Fin (Fintype.card (Σ i, Fin (n i))),
      d i ∣ (A.submatrix (Sigma.mk i) ((Fintype.equivFin _).symm ∘ j)).det) :
    (∏ i, d i) ∣ A.det := by
  classical
  let e := Fintype.equivFin (Σ i, Fin (n i))
  let M := fun i => A.submatrix (Sigma.mk i) e.symm
  choose C R hR using fun i => integer_square_column_factorization (M i)
  let B := fun i => M i * C i
  have hdiv (i : Fin c) : d i ∣ (B i).det :=
    (Finset.dvd_gcd (fun j _ => hd i j)).trans
      (Int.Matrix.minorGcd_dvd_det_mul _ _)
  let Q : Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℤ :=
    fun i j => R i.1 i.2 (e j)
  have hfac : Matrix.blockDiagonal' B * Q = A := by
    ext ⟨i, j⟩ l
    rw [Matrix.mul_apply, Fintype.sum_sigma]
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.blockDiagonal'_apply_eq]
      simpa only [M, B, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.mul_apply, Q] using (congrArg (fun m => m j (e l)) (hR i))
    · intro k _ hki
      apply Finset.sum_eq_zero
      intro t _
      rw [Matrix.blockDiagonal'_apply_ne B j t hki.symm, zero_mul]
    · simp
  rw [← hfac, Matrix.det_mul, Matrix.det_blockDiagonal']
  exact dvd_mul_of_dvd_left (Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hdiv i)) _

/-- Enumerate rows grouped by their residue-class label. -/
private def partitionRowEquiv :
    (Σ i : Fin c, Fin (Fintype.card {j : Fin s // label j = i})) ≃ Fin s :=
  (Equiv.sigmaCongrRight fun i =>
    (Fintype.equivFin {j : Fin s // label j = i}).symm).trans (Equiv.sigmaFiberEquiv label)

/-- An enumeration of the rows `j` with `label j = i`, the `i`-th block of the partition of the rows
determined by `label`. -/
def residueRows :
    Fin (Fintype.card {j : Fin s // label j = i}) → Fin s :=
  fun j => ((Fintype.equivFin {j : Fin s // label j = i}).symm j).val

/-- Every row enumerated by `residueRows label i` has label `i`. -/
lemma residueRows_label
    (j : Fin (Fintype.card {j : Fin s // label j = i})) :
    label (residueRows label i j) = i :=
  ((Fintype.equivFin {j : Fin s // label j = i}).symm j).property

/-- The sizes of the classes of a labelling `label : Fin s → Fin c` add up to `s`. -/
lemma sum_residue_class_sizes :
    (∑ i : Fin c, Fintype.card {j : Fin s // label j = i}) = s := by
  simpa using (Fintype.card_congr (partitionRowEquiv label))

/-- Divisibility of all local block minors combines for an arbitrary row
partition, without any assumption on the ordering of residue classes. -/
private theorem residue_minor_divisors_dvd_det
    (A : Matrix (Fin s) (Fin s) ℤ) (label : Fin s → Fin c) (d : Fin c → ℤ)
    (hd : ∀ i, ∀ j : Fin (Fintype.card {j : Fin s // label j = i}) → Fin s,
      d i ∣ (A.submatrix (residueRows label i) j).det) :
    (∏ i, d i) ∣ A.det := by
  classical
  rw [← Matrix.det_submatrix_equiv_self (partitionRowEquiv label) A]
  apply block_minor_divisors_dvd_det
  solve_by_elim

/-- If each `d i` divides every maximal minor of the rows labelled `i`, then `∏ i, d i`
divides the gcd of all maximal minors of the rectangular matrix. -/
private theorem residue_minor_divisors_dvd_minorGcd (d : Fin c → ℤ)
    (hd : ∀ i, ∀ j : Fin (Fintype.card {j : Fin s // label j = i}) → Fin N,
      d i ∣ (A.submatrix (residueRows label i) j).det) :
    (∏ i, d i) ∣ Int.Matrix.minorGcd A := by
  classical
  apply Finset.dvd_gcd
  intro S _
  apply residue_minor_divisors_dvd_det _ label d
  intro i j
  exact hd i _

/-- If the rows of an integer matrix `A` are partitioned into blocks by `label`, and for each block
`i` the power `p ^ e i` divides every maximal minor of the block's rows, then `p ^ (∑ i, e i)`
divides the gcd of the maximal minors of `A`. -/
theorem residue_prime_powers_dvd_minorGcd
    (p : ℤ) (e : Fin c → ℕ)
    (he : ∀ i, ∀ j : Fin (Fintype.card {j : Fin s // label j = i}) → Fin N,
      p ^ e i ∣ (A.submatrix (residueRows label i) j).det) :
    p ^ (∑ i, e i) ∣ Int.Matrix.minorGcd A := by
  simpa [Finset.prod_pow_eq_pow_sum] using residue_minor_divisors_dvd_minorGcd A label (fun i => p ^ e i) he

end
end CCDN
