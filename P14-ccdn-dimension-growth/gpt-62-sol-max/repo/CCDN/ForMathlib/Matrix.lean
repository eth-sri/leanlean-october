/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Minors and determinants of matrices

Nonzero minors of matrices with arbitrarily many rows: the row index type may be infinite, as
for coefficient matrices indexed by all monomials; only the column index type is finite.

## Main results

* `Matrix.exists_fin_linearIndependent_row_span_eq`: finitely many linearly independent rows
  span the row space.
* `Matrix.exists_rank_linearIndependent_rows`: there are `A.rank` linearly independent rows.
* `Matrix.hasNonzeroMinor_of_le_rank`: every `r ≤ A.rank` is witnessed by a
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

/-- A finite independent family spans the rows even when their original index
set is infinite. -/
theorem exists_fin_linearIndependent_row_span_eq
    {F ι ν : Type*} [Field F] [Fintype ν] (A : Matrix ι ν F) :
    ∃ (s : ℕ) (a : Fin s → ι),
      LinearIndependent F (A.submatrix a id).row ∧
      Submodule.span F (Set.range (A.submatrix a id).row) =
        Submodule.span F (Set.range A.row) := by
  classical
  obtain ⟨κ, a, _, hs, hi⟩ := exists_linearIndependent' F A.row
  let : Finite κ := hi.finite
  let : Fintype κ := Fintype.ofFinite κ
  let e := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ, a ∘ e, hi.comp e e.injective, ?_⟩
  have hr : Set.range (A.submatrix (a ∘ e) id).row = Set.range (A.row ∘ a) := by
    exact id (Function.Surjective.range_comp (Equiv.surjective e) (A.row ∘ a))
  simp_all

private lemma mem_ker_mulVecLin_iff_span_row {F ι ν : Type*} [Field F] [Fintype ν]
    (A : Matrix ι ν F) (v : ν → F) :
    v ∈ A.mulVecLin.ker ↔ Submodule.span F (Set.range A.row) ≤ ((dotProductBilin F F).flip v).ker := by
  rw [Submodule.span_le, Set.range_subset_iff, LinearMap.mem_ker]
  simp [funext_iff, mulVec, Matrix.row]

/-- Restriction to spanning rows preserves the exact kernel. -/
theorem ker_mulVecLin_submatrix_eq_of_span_row_eq
    {F ι κ ν : Type*} [Field F] [Fintype ν] (A : Matrix ι ν F) (a : κ → ι)
    (hs : Submodule.span F (Set.range (A.submatrix a id).row) =
      Submodule.span F (Set.range A.row)) :
    (A.submatrix a id).mulVecLin.ker = A.mulVecLin.ker := by
  ext v
  simp only [mem_ker_mulVecLin_iff_span_row, hs]

/-- There are exactly rank-many independent rows. -/
private theorem exists_rank_linearIndependent_rows
    {F ι ν : Type*} [Field F] [Fintype ν] (A : Matrix ι ν F) :
    ∃ a : Fin A.rank → ι, LinearIndependent F (A.submatrix a id).row := by
  obtain ⟨s, a, hi, hs⟩ := exists_fin_linearIndependent_row_span_eq A
  have h₁ := (A.submatrix a id).mulVecLin.finrank_range_add_finrank_ker
  have h₂ := A.mulVecLin.finrank_range_add_finrank_ker
  change (A.submatrix a id).rank + _ = _ at h₁
  change A.rank + _ = _ at h₂
  rw [hi.rank_matrix, Fintype.card_fin, ker_mulVecLin_submatrix_eq_of_span_row_eq A a hs] at h₁
  have hr : s = A.rank := by omega
  subst s
  exact ⟨a, hi⟩

/-- Full row rank supplies a nonzero square minor: some set of columns of the transpose is
linearly independent. -/
theorem exists_det_submatrix_ne_zero_of_linearIndependent_row
    {F ν : Type*} [Field F] [Fintype ν] {s : ℕ}
    (A : Matrix (Fin s) ν F) (hi : LinearIndependent F A.row) :
    ∃ c : Fin s → ν, (A.submatrix id c).det ≠ 0 := by
  have hr : Aᵀ.rank = s := by rw [rank_transpose, hi.rank_matrix, Fintype.card_fin]
  obtain ⟨c, hli⟩ := exists_rank_linearIndependent_rows Aᵀ
  let e := finCongr hr
  refine ⟨c ∘ e.symm, ?_⟩
  rw [← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det]
  exact linearIndependent_col_iff_isUnit.mp (hli.comp e.symm e.symm.injective)

/-- A nonzero `k × k` minor shows that a matrix over a domain has rank at least `k`. -/
theorem le_rank_of_det_submatrix_ne_zero {R ι ν : Type*} [CommRing R] [IsDomain R] [Fintype ν]
    {k : ℕ} (A : Matrix ι ν R) (r : Fin k → ι) (c : Fin k → ν)
    (h : (A.submatrix r c).det ≠ 0) : k ≤ A.rank := by
  simpa [rank_of_det_ne_zero h, Fintype.card_fin] using A.rank_submatrix_le r c

/-- `A` has a nonzero `r × r` minor: some choice of `r` rows and `r` columns of `A` whose
square submatrix has nonzero determinant. The chosen rows and columns are automatically
distinct (`Matrix.injective_rows_of_det_submatrix_ne_zero`,
`Matrix.injective_cols_of_det_submatrix_ne_zero`). -/
def HasNonzeroMinor {R ι ν : Type*} [CommRing R] (A : Matrix ι ν R) (r : ℕ) : Prop :=
  ∃ (a : Fin r → ι) (c : Fin r → ν), (A.submatrix a c).det ≠ 0

/-- Every rank lower bound over a field is witnessed by a nonzero minor. -/
theorem hasNonzeroMinor_of_le_rank {F ι ν : Type*} [Field F] [Fintype ν] (A : Matrix ι ν F)
    {r : ℕ} (hr : r ≤ A.rank) : A.HasNonzeroMinor r := by
  obtain ⟨a, hi⟩ := exists_rank_linearIndependent_rows A
  exact ⟨a ∘ Fin.castLE hr, exists_det_submatrix_ne_zero_of_linearIndependent_row _
    (hi.comp _ (Fin.castLE_injective hr))⟩

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
  let I := Ideal.span {m}
  let φ := Ideal.Quotient.mk I
  have he : A.map φ = B.map φ := by
    ext i j
    apply sub_eq_zero.mp
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h i j))
  apply Ideal.mem_span_singleton.mp
  change A.det - B.det ∈ I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change φ (A.det - B.det) = 0
  rw [map_sub, φ.map_det, φ.map_det]
  change (A.map φ).det - (B.map φ).det = 0
  rw [he, sub_self]

/-- Divisibility of all maximal row minors is preserved by taking square row combinations.
Expand the determinant by multilinearity; terms with repeated rows vanish. -/
theorem dvd_det_mul_of_row_minors {R ι : Type*} [CommRing R] [Fintype ι] {s : ℕ}
    (U : Matrix (Fin s) ι R) (V : Matrix ι (Fin s) R) {d : R}
    (h : ∀ t : Fin s ↪ ι, d ∣ (V.submatrix t id).det) : d ∣ (U * V).det := by
  classical
  have he : U * V = fun i => ∑ j, U i j • V j := by
    ext i k
    simp [mul_apply]
  change d ∣ detRowAlternating.toMultilinearMap (U * V)
  rw [he, MultilinearMap.map_sum]
  refine Finset.dvd_sum fun t _ => ?_
  change d ∣ (Matrix.of fun i j => U i (t i) * V (t i) j).det
  rw [show (Matrix.of fun i j => U i (t i) * V (t i) j) =
    Matrix.of (fun i j => U i (t i) * (V.submatrix t id) i j) from rfl, det_mul_column]
  by_cases ht : Function.Injective t
  · exact dvd_mul_of_dvd_right (h ⟨t, ht⟩) _
  · obtain ⟨i, j, e, hn⟩ := Function.not_injective_iff.mp ht
    rw [det_zero_of_row_eq (M := V.submatrix t id) hn (funext fun k => congrArg (fun l => V l k) e), mul_zero]
    exact dvd_zero _

end Matrix
