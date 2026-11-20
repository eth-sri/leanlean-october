/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.IntegerMinors

/-! Combining maximal-minor divisibility across row blocks. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix Module Finset

/-- The product of common divisors of the maximal minors of disjoint row blocks
is a divisor of the full determinant. Empty and rank-deficient blocks are allowed. -/
private theorem block_minor_divisors_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → ℕ)
    (A : Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℤ) (d : ι → ℤ)
    (hd : ∀ i, ∀ j : Fin (n i) ↪ (Σ i, Fin (n i)),
      d i ∣ (A.submatrix (Sigma.mk i) j).det) :
    (∏ i, d i) ∣ A.det := by
  classical
  let M := fun i => A.submatrix (Sigma.mk i) id
  choose B R C hR hC using fun i => integer_square_column_factorization (M i)
  have hdiv (i : ι) : d i ∣ (B i).det := by
    rw [hC i]
    apply dvd_det_square_column_factor
    intro j
    exact hd i j
  let Q : Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℤ :=
    fun i j => R i.1 i.2 j
  have hfac : Matrix.blockDiagonal' B * Q = A := by
    ext ⟨i, j⟩ l
    rw [Matrix.mul_apply, Fintype.sum_sigma]
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.blockDiagonal'_apply_eq]
      have hh := (congrArg (fun m => m j l) (hR i)).symm
      simpa only [M, Matrix.submatrix_apply, id_eq, Matrix.mul_apply, Q] using hh
    · intro k _ hki
      apply Finset.sum_eq_zero
      intro t _
      rw [Matrix.blockDiagonal'_apply_ne B j t hki.symm, zero_mul]
    · simp
  rw [← hfac, Matrix.det_mul, Matrix.det_blockDiagonal']
  exact dvd_mul_of_dvd_left (Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hdiv i)) _

/-- Enumerate rows grouped by their residue-class label. -/
private def partitionRowEquiv {ι : Type*} [DecidableEq ι] {s : ℕ} (label : Fin s → ι) :
    (Σ i : ι, Fin (Fintype.card {j : Fin s // label j = i})) ≃ Fin s :=
  (Equiv.sigmaCongrRight fun i =>
    (Fintype.equivFin {j : Fin s // label j = i}).symm).trans (Equiv.sigmaFiberEquiv label)

/-- An enumeration of the rows `j` with `label j = i`, the `i`-th block of the partition of the rows
determined by `label`. -/
def residueRows {ι : Type*} [DecidableEq ι] {s : ℕ} (label : Fin s → ι) (i : ι) :
    Fin (Fintype.card {j : Fin s // label j = i}) → Fin s :=
  fun j => ((Fintype.equivFin {j : Fin s // label j = i}).symm j).val

/-- Every row enumerated by `residueRows label i` has label `i`. -/
lemma residueRows_label {ι : Type*} [DecidableEq ι] {s : ℕ} (label : Fin s → ι) (i : ι)
    (j : Fin (Fintype.card {j : Fin s // label j = i})) :
    label (residueRows label i j) = i :=
  ((Fintype.equivFin {j : Fin s // label j = i}).symm j).property

/-- The sizes of the classes of a labelling `label : Fin s → ι` add up to `s`. -/
lemma sum_residue_class_sizes {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ} (label : Fin s → ι) :
    (∑ i : ι, Fintype.card {j : Fin s // label j = i}) = s := by
  have h := Fintype.card_congr (partitionRowEquiv label)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

/-- Divisibility of all local block minors combines for an arbitrary row
partition, without any assumption on the ordering of residue classes. -/
private theorem residue_minor_divisors_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℤ) (label : Fin s → ι) (d : ι → ℤ)
    (hd : ∀ i, ∀ j : Fin (Fintype.card {j : Fin s // label j = i}) → Fin s,
      d i ∣ (A.submatrix (residueRows label i) j).det) :
    (∏ i, d i) ∣ A.det := by
  classical
  let e := partitionRowEquiv label
  rw [← Matrix.det_submatrix_equiv_self e A]
  apply block_minor_divisors_dvd_det
  intro i j
  exact hd i (e ∘ j)

/-- If the rows of an integer matrix `A` are partitioned into blocks by `label`, and for each block
`i` the power `p ^ e i` divides every maximal minor of the block's rows, then `p ^ (∑ i, e i)`
divides the gcd of the maximal minors of `A`. -/
theorem residue_prime_powers_dvd_minorGcd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s N : ℕ} (A : Matrix (Fin s) (Fin N) ℤ) (label : Fin s → ι)
    (p : ℤ) (e : ι → ℕ)
    (he : ∀ i, ∀ j : Fin (Fintype.card {j : Fin s // label j = i}) → Fin N,
      p ^ e i ∣ (A.submatrix (residueRows label i) j).det) :
    p ^ (∑ i, e i) ∣ minorGcd A := by
  rw [← Finset.prod_pow_eq_pow_sum, dvd_minorGcd]
  intro j
  exact residue_minor_divisors_dvd_det _ label (fun i => p ^ e i) (fun i c => he i (j ∘ c))

end
end CCDN
