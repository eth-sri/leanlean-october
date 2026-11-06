module

public import GradedNear.Defs

/-!
# Binning a near row (paper §§8.6, 10)

A near row of a leaf LP relaxes the threshold form (T) of the configuration's entries. Each
entry is assigned to a column (bin) of the leaf, to a fixed family term of the row, or to
nothing. The assignment must be conservative:

* the bin's feature is at most the entry's feature, or at most `0` (such a bin contributes
  nothing at `τ ≥ 0`);
* the bin's diagonal is at least the entry's diagonal;
* the row's radius is at least the configuration's radius;
* each family term has at least its count of entries.

Then (T) at a threshold `τ` implies row `k` of the leaf LP at `τ`, for column values shared by
all rows that do not exceed the bin counts on the columns with a positive feature in row `k`.
`near_row_of_bins` states this in the exact form of `GradedNear.Cert.Feasible`.
-/

@[expose] public section

namespace GradedNear.Cert

open Finset

/-- A threshold term `(v - τ)_+² / D` at `τ ≥ 0` increases with `v` and decreases with `D > 0`,
and it vanishes for `v ≤ 0`. -/
lemma term_le {v v' D D' τ : ℝ} (hv : v ≤ v' ∨ v ≤ 0) (hτ : 0 ≤ τ) (hD' : 0 < D')
    (hDD : D' ≤ D) : (max 0 (v - τ)) ^ 2 / D ≤ (max 0 (v' - τ)) ^ 2 / D' := by
  rcases hv with hv | hv
  · gcongr
  · rw [max_eq_left (by linarith)]
    simp
    positivity

lemma bin_le {ι : Type*} {F : Finset ι} {v Dg : ι → ℝ} {n τ : ℝ} {a b : ℤ} (hτ : 0 ≤ τ)
    (hDg : ∀ j, 0 < Dg j) (hn : 0 < a → n ≤ F.card) (h0 : 0 ≤ n ∨ 0 < b)
    (hF : ∀ j ∈ F, ((a : ℝ) / S ≤ v j ∨ a ≤ 0) ∧ Dg j ≤ (b : ℝ) / S) :
    n * (max 0 ((a : ℝ) / S - τ)) ^ 2 / ((b : ℝ) / S) ≤
      ∑ j ∈ F, (max 0 (v j - τ)) ^ 2 / Dg j := by
  have hS : (0 : ℝ) < S := by norm_num [S]
  have hs := sum_nonneg fun j (_ : j ∈ F) => div_nonneg (sq_nonneg (max 0 (v j - τ))) (hDg j).le
  rcases le_or_gt ((a : ℝ) / S) τ with hV | hV
  · simp_all
  have ha : 0 < a := mod_cast (div_pos_iff_of_pos_right hS).1 (hτ.trans_lt hV)
  have hn := hn ha
  rcases F.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · simp at hn
    rcases h0 with h0 | h0
    · simp [le_antisymm hn h0]
    · simpa using div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn (sq_nonneg _))
        (by positivity)
  have : 0 ≤ (b : ℝ) / S := (hDg j).le.trans (hF j hj).2
  grw [hn, mul_div_assoc, ← nsmul_eq_mul, ← sum_const]
  exact sum_le_sum fun j hj => term_le ((hF j hj).1.imp_right fun h =>
      div_nonpos_of_nonpos_of_nonneg (mod_cast h) hS.le) hτ (hDg j) (hF j hj).2

/-- **A near row of the leaf LP from the threshold form.** Let the entries `j : ι` of row `k` satisfy
(T): `τ ∈ [0, √d]` and `Σ_j (v_j - τ)_+² / D_j ≤ 1 - τ²/d`, with `D_j > 0`. Assign each entry by
`bin` to a column of the leaf, to a family term of row `k`, or to nothing, conservatively:
* a binned entry's feature is at least its bin's feature, or the bin's feature is `≤ 0`;
* a binned entry's diagonal is at most its bin's diagonal;
* each family term `(n, v, D)` has `D > 0` and at least `n` entries;
* the row's radius is at least `d`.

Let `x ≥ 0` be column values shared by all rows (the LP point). If every column with a positive
feature in row `k` has `x_c` at most the number of entries of row `k` binned to it, then row `k`
of `Feasible` holds at `x` and `τ`. (Columns whose feature in row `k` is `≤ 0` contribute nothing,
so their `x_c` is free; with `x_c` equal to the bin counts this is the row at the counts.) -/
theorem near_row_of_bins (L : Leaf) (k : ℕ) {ι : Type*} [Fintype ι] (v Dg : ι → ℝ) (d τ : ℝ)
    (hDg : ∀ j, 0 < Dg j) (hd : 0 < d) (hτ0 : 0 ≤ τ) (hτd : τ ≤ Real.sqrt d)
    (hT : ∑ j, (max 0 (v j - τ)) ^ 2 / Dg j ≤ 1 - τ ^ 2 / d)
    (bin : ι → Option (Fin L.cols.length ⊕ Fin (L.rows.getD k ⟨1, []⟩).fam.length))
    (hcol : ∀ j c, bin j = some (Sum.inl c) →
      (((L.cols.get c).v.getD k 0 : ℝ) / S ≤ v j ∨ (L.cols.get c).v.getD k 0 ≤ 0) ∧
        Dg j ≤ ((L.cols.get c).D.getD k 1 : ℝ) / S)
    (hfam : ∀ j i, bin j = some (Sum.inr i) →
      (((((L.rows.getD k ⟨1, []⟩).fam.get i).2.1 : ℤ) : ℝ) / S ≤ v j ∨
          ((L.rows.getD k ⟨1, []⟩).fam.get i).2.1 ≤ 0) ∧
        Dg j ≤ ((((L.rows.getD k ⟨1, []⟩).fam.get i).2.2 : ℤ) : ℝ) / S)
    (hfamD : ∀ i, 0 < ((L.rows.getD k ⟨1, []⟩).fam.get i).2.2)
    (hn : ∀ i, ((((L.rows.getD k ⟨1, []⟩).fam.get i).1 : ℤ) : ℝ) ≤
      ((univ.filter fun j => bin j = some (Sum.inr i)).card : ℝ))
    (hdrow : d ≤ ((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)
    (x : Fin L.cols.length → ℝ) (hx0 : ∀ c, 0 ≤ x c)
    (hx : ∀ c, 0 < (L.cols.get c).v.getD k 0 →
      x c ≤ ((univ.filter fun j => bin j = some (Sum.inl c)).card : ℝ)) :
    0 ≤ τ ∧ τ ^ 2 ≤ ((L.rows.getD k ⟨1, []⟩).d : ℝ) / S ∧
      rowLHS L x k τ ≤ 1 - τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S) := by
  have hτ2 : τ ^ 2 ≤ d := by grind [pow_le_pow_left₀]
  have := div_le_div_of_nonneg_left (sq_nonneg τ) hd hdrow
  rw [← sum_fiberwise univ bin, Fintype.sum_option, Fintype.sum_sum_type] at hT
  have hnone := sum_nonneg fun j (_ : j ∈ univ.filter (fun j => bin j = none)) =>
    div_nonneg (sq_nonneg (max 0 (v j - τ))) (hDg j).le
  have hcols := sum_le_sum fun c (_ : c ∈ univ) => bin_le hτ0 hDg (hx c) (.inl (hx0 c))
    fun j hj => hcol j c (mem_filter.1 hj).2
  have hfams := sum_le_sum fun i (_ : i ∈ univ) => bin_le hτ0 hDg (fun _ => hn i)
    (.inr (hfamD i)) fun j hj => hfam j i (mem_filter.1 hj).2
  unfold rowLHS
  rw [← Fin.sum_univ_fun_getElem]
  grind

end GradedNear.Cert
