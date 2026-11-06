/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Minors and determinants of matrices

Nonzero minors of matrices with arbitrarily many rows: the row index type may be infinite, as
for coefficient matrices indexed by all monomials; only the column index type is finite.

## Main results

* `Matrix.exists_fin_linearIndependent_row_span_eq`: finitely many linearly independent rows
  span the row space.
* `Matrix.exists_rank_linearIndependent_rows`: there are `A.rank` linearly independent rows.
* `Matrix.exists_det_submatrix_ne_zero_of_le_rank`: every `r ≤ A.rank` is witnessed by a
  nonzero `r × r` minor with distinct rows and columns.
* `Matrix.le_rank_of_det_submatrix_ne_zero`: conversely, a nonzero `k × k` minor shows
  `k ≤ A.rank`.
* `Matrix.HasNonzeroMinor`: the predicate that some `r × r` minor is nonzero; its rows and
  columns are automatically distinct (`Matrix.injective_rows_of_det_submatrix_ne_zero`,
  `Matrix.injective_cols_of_det_submatrix_ne_zero`).
* `Matrix.det_blockDiagonal'`: the determinant of `blockDiagonal' M` is the product of the
  determinants of the blocks. Mathlib computes `Matrix.det_blockDiagonal` for blocks of a common
  size; here the blocks may have different sizes.
* `Matrix.dvd_det_sub_det_of_dvd_sub`: entrywise congruence of integer matrices implies
  congruence of their determinants.
-/

@[expose] public section

namespace Matrix

variable {F ι ν : Type*} [Field F] [Fintype ν]

/-- A finite independent family spans the rows even when their original index
set is infinite. -/
theorem exists_fin_linearIndependent_row_span_eq
     (A : Matrix ι ν F) :
    ∃ (s : ℕ) (a : Fin s → ι), Function.Injective a ∧
      LinearIndependent F (A.submatrix a id).row ∧
      Submodule.span F (Set.range (A.submatrix a id).row) =
        Submodule.span F (Set.range A.row) := by
  classical
  obtain ⟨κ, a, ha, hs, hi⟩ := exists_linearIndependent' F A.row
  let : Finite κ := hi.finite
  let : Fintype κ := Fintype.ofFinite κ
  let e := (Fintype.equivFin κ).symm
  have hli := hi.comp e e.injective
  refine ⟨Fintype.card κ, a ∘ e, ha.comp e.injective, hli, ?_⟩
  have hr : Set.range (A.submatrix (a ∘ e) id).row = Set.range (A.row ∘ a) := by
    exact id (Function.Surjective.range_comp (Equiv.surjective e) (A.row ∘ a))
  rw [hr, hs]


/-- There are exactly rank-many independent rows. -/
theorem exists_rank_linearIndependent_rows
     (A : Matrix ι ν F) :
    ∃ a : Fin A.rank → ι, Function.Injective a ∧
      LinearIndependent F (A.submatrix a id).row := by
  obtain ⟨s, a, ha, hi, hs⟩ := exists_fin_linearIndependent_row_span_eq A
  have hk := (show (A.submatrix a id).mulVecLin.ker = A.mulVecLin.ker from (by
               ext v
               constructor
               · intro hv
                 ext i
                 have hm : A.row i ∈ Submodule.span F (Set.range (A.submatrix a id).row) := by
                   aesop
                 suffices hh : ∀ r ∈ Submodule.span F (Set.range (A.submatrix a id).row), r ⬝ᵥ v = 0 from hh _ hm
                 intro r hr
                 induction hr using Submodule.span_induction with
                 | mem r hr =>
                   obtain ⟨j, rfl⟩ := hr
                   exact congrFun hv j
                 | zero => simp
                 | add x y hx hy ihx ihy => simp [add_dotProduct, ihx, ihy]
                 | smul b x hx ih => simp [smul_dotProduct, ih]
               · intro hv
                 ext i
                 exact congrFun hv (a i)))
  have h₁ := (A.submatrix a id).mulVecLin.finrank_range_add_finrank_ker
  have h₂ := A.mulVecLin.finrank_range_add_finrank_ker
  change (A.submatrix a id).rank + _ = _ at h₁
  change A.rank + _ = _ at h₂
  rw [hi.rank_matrix, Fintype.card_fin, hk] at h₁
  have he : s = A.rank := by omega
  subst s
  exact ⟨a, ha, hi⟩

/-- Full row rank supplies a nonzero square minor: some set of columns of the transpose is
linearly independent. -/
theorem exists_det_submatrix_ne_zero_of_linearIndependent_row
    {F ν : Type*} [Field F] [Fintype ν] {s : ℕ}
    (A : Matrix (Fin s) ν F) (hi : LinearIndependent F A.row) :
    ∃ c : Fin s → ν, Function.Injective c ∧ (A.submatrix id c).det ≠ 0 := by
  have hr : Aᵀ.rank = s := by rw [rank_transpose, hi.rank_matrix, Fintype.card_fin]
  obtain ⟨c, hc, hli⟩ := exists_rank_linearIndependent_rows Aᵀ
  let e := finCongr hr
  refine ⟨c ∘ e.symm, hc.comp e.symm.injective, ?_⟩
  have hcol :=
    hli.comp e.symm e.symm.injective
  rw [← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det]
  exact linearIndependent_col_iff_isUnit.mp hcol

/-- Every rank lower bound is witnessed by a nonzero minor with distinct rows
and distinct columns, without any finiteness requirement on the rows. -/
theorem exists_det_submatrix_ne_zero_of_le_rank
     (A : Matrix ι ν F)
    (r : ℕ) (hr : r ≤ A.rank) :
    ∃ (a : Fin r → ι) (c : Fin r → ν), Function.Injective a ∧
      Function.Injective c ∧ (A.submatrix a c).det ≠ 0 := by
  obtain ⟨a, ha, hi⟩ := exists_rank_linearIndependent_rows A
  let b : Fin r → Fin A.rank := Fin.castLE hr
  have hb := Fin.castLE_injective hr
  have hli := hi.comp b hb
  obtain ⟨c, hc, hd⟩ := exists_det_submatrix_ne_zero_of_linearIndependent_row _ hli
  exact ⟨a ∘ b, c, ha.comp hb, hc, hd⟩

/-- A nonzero `k × k` minor shows that a matrix over a domain has rank at least `k`. -/
theorem le_rank_of_det_submatrix_ne_zero {R ι ν : Type*} [CommRing R] [IsDomain R] [Fintype ν]
    {k : ℕ} (A : Matrix ι ν R) (r : Fin k → ι) (c : Fin k → ν)
    (h : (A.submatrix r c).det ≠ 0) : k ≤ A.rank := by
  simpa only [rank_of_det_ne_zero h, Fintype.card_fin] using A.rank_submatrix_le r c

/-- `A` has a nonzero `r × r` minor: some choice of `r` rows and `r` columns of `A` whose
square submatrix has nonzero determinant. The chosen rows and columns are automatically
distinct (`Matrix.injective_rows_of_det_submatrix_ne_zero`,
`Matrix.injective_cols_of_det_submatrix_ne_zero`). -/
def HasNonzeroMinor {R ι ν : Type*} [CommRing R] (A : Matrix ι ν R) (r : ℕ)  :=
  ∃ (a : Fin r → ι) (c : Fin r → ν), (A.submatrix a c).det ≠ 0

/-- Every rank lower bound over a field is witnessed by a nonzero minor. -/
theorem hasNonzeroMinor_of_le_rank  (A : Matrix ι ν F)
    {r : ℕ} (hr : r ≤ A.rank) : A.HasNonzeroMinor r :=
  let ⟨a, c, _, _, h⟩ := exists_det_submatrix_ne_zero_of_le_rank A r hr
  ⟨a, c, h⟩

variable {o R : Type*} {m' : o → Type*} [Fintype o] [DecidableEq o]
  [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommRing R]

/-- The determinant of a block-diagonal matrix with blocks of varying sizes is the product of
the determinants of its blocks. -/
theorem det_blockDiagonal' (M : ∀ i, Matrix (m' i) (m' i) R) :
    (blockDiagonal' M).det = ∏ i, (M i).det := by
  classical
  let _ : LinearOrder o := LinearOrder.lift' (Fintype.equivFin o) (Fintype.equivFin o).injective
  rw [(blockTriangular_blockDiagonal' M).det_fintype]
  refine Finset.prod_congr rfl fun i _ => ?_
  let e := (Equiv.sigmaSubtype (β := m') i).symm
  have he : ((blockDiagonal' M).toSquareBlock Sigma.fst i).submatrix e e = M i := by
    ext j k
    exact blockDiagonal'_apply_eq M i j k
  rw [← he, det_submatrix_equiv_self]

/-- Entrywise congruence implies determinant congruence, for every modulus. -/
theorem dvd_det_sub_det_of_dvd_sub {s : ℕ} (A B : Matrix (Fin s) (Fin s) ℤ)
    (m : ℤ) (h : ∀ i j, m ∣ A i j - B i j) : m ∣ A.det - B.det := by
  let I : Ideal ℤ := Ideal.span {m}
  let φ := Ideal.Quotient.mk I
  have he : A.map φ = B.map φ := by
    exact ext fun i j => sub_eq_zero.mp (id (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h i j))))
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, φ.map_det, φ.map_det]
  change (A.map φ).det - (B.map φ).det = 0
  rw [he, sub_self]

end Matrix
