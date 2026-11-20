module

public import GradedNear.Cert.Rows

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
  have h : max 0 (v - τ) ≤ max 0 (v' - τ) := by grind
  gcongr

-- The same fiber estimate applies to both a variable column and a fixed family.
lemma count_le {ι : Type*} (s : Finset ι) (t : ι → ℝ) (ht : ∀ j, 0 ≤ t j)
    {w v D τ : ℝ} (hτ : 0 ≤ τ) (hw : 0 < v → w ≤ s.card)
    (he : 0 ≤ w ∨ 0 ≤ D)
    (h : ∀ j ∈ s, max 0 (v - τ) ^ 2 / D ≤ t j) :
    w * max 0 (v - τ) ^ 2 / D ≤ ∑ j ∈ s, t j := by
  rw [mul_div_assoc]
  have hsum : 0 ≤ ∑ j ∈ s, t j := sum_nonneg fun j _ => ht j
  rcases le_or_gt v 0 with hv | hv
  · simpa [max_eq_left (sub_nonpos.mpr (hv.trans hτ))] using hsum
  rcases le_or_gt 0 (max 0 (v - τ) ^ 2 / D) with hq | hq
  · exact (mul_le_mul_of_nonneg_right (hw hv) hq).trans (by simpa using sum_le_sum h)
  · exact (mul_nonpos_of_nonneg_of_nonpos (he.resolve_right fun _ => hq.not_ge (by positivity)) hq.le).trans hsum

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
    (bin : ι → Option (Fin L.cols.length ⊕ Fin (rowAt L k).fam.length))
    (hcol : ∀ j c, bin j = some (Sum.inl c) →
      (unscaled (featureAt (L.cols.get c) k) ≤ v j ∨ featureAt (L.cols.get c) k ≤ 0) ∧
        Dg j ≤ unscaled (diagAt (L.cols.get c) k))
    (hfam : ∀ j i, bin j = some (Sum.inr i) →
      (unscaled ((familyAt L k i).2.1) ≤ v j ∨
          (familyAt L k i).2.1 ≤ 0) ∧
        Dg j ≤ unscaled ((familyAt L k i).2.2))
    (hfamD : ∀ i, 0 < (familyAt L k i).2.2)
    (hn : ∀ i, ((familyAt L k i).1 : ℝ) ≤
      ((univ.filter fun j => bin j = some (Sum.inr i)).card : ℝ))
    (hdrow : d ≤ unscaled ((rowAt L k).d))
    (x : Fin L.cols.length → ℝ) (hx0 : ∀ c, 0 ≤ x c)
    (hx : ∀ c, 0 < featureAt (L.cols.get c) k →
      x c ≤ ((univ.filter fun j => bin j = some (Sum.inl c)).card : ℝ)) :
    0 ≤ τ ∧ τ ^ 2 ≤ unscaled ((rowAt L k).d) ∧
      rowLHS L x k τ ≤ 1 - τ ^ 2 / (unscaled ((rowAt L k).d)) := by
  refine ⟨hτ0, ((Real.le_sqrt hτ0 hd.le).mp hτd).trans hdrow, ?_⟩
  let t (j : ι) := max 0 (v j - τ) ^ 2 / Dg j
  have ht j : 0 ≤ t j := div_nonneg (sq_nonneg _) (hDg j).le
  have hbin j {v₀ D₀ : ℤ} (h : (unscaled v₀ ≤ v j ∨ v₀ ≤ 0) ∧ Dg j ≤ unscaled D₀) :
      max 0 (unscaled v₀ - τ) ^ 2 / (unscaled D₀) ≤ t j :=
    term_le (h.1.imp_right fun e => div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast e) S_pos.le)
      hτ0 (hDg j) h.2
  refine le_trans (b := ∑ j, t j) ?_ (hT.trans ?_)
  · rw [← sum_fiberwise univ bin t, Fintype.sum_option, Fintype.sum_sum_type, rowLHS, ← Fin.sum_univ_fun_getElem]
    refine (add_le_add (sum_le_sum fun c _ => ?_) (sum_le_sum fun i _ => ?_)).trans
      (le_add_of_nonneg_left (sum_nonneg fun j _ => ht j))
    · exact count_le _ t ht hτ0 (fun h => hx c (by exact_mod_cast (div_pos_iff_of_pos_right S_pos).mp h))
        (.inl (hx0 c)) (fun j hj => hbin j (hcol j c (mem_filter.mp hj).2))
    · exact count_le _ t ht hτ0 (fun _ => hn i) (.inr (unscaled_nonneg (hfamD i).le))
        (fun j hj => hbin j (hfam j i (mem_filter.mp hj).2))
  · gcongr

end GradedNear.Cert
