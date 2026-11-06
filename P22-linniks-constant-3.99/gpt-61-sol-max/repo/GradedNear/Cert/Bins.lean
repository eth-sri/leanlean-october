import GradedNear.Tactics
import GradedNear.Defs

set_option quotPrecheck false

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

namespace GradedNear.Cert

open Finset

lemma unscale_nonpos {v : ℤ} (hv : v ≤ 0) : unscale v ≤ 0 := by
  norm_num [S]
  grind [Int.cast_nonpos]

/-- A threshold term `(v - τ)_+² / D` at `τ ≥ 0` increases with `v` and decreases with `D > 0`,
and it vanishes for `v ≤ 0`. -/
lemma term_le {v v' D D' τ : ℝ} (hv : v ≤ v' ∨ v ≤ 0) (hτ : 0 ≤ τ) (hD' : 0 < D')
    (hDD : D' ≤ D) : max 0 (v - τ) ^ 2 / D ≤ max 0 (v' - τ) ^ 2 / D' := by
  bound

variable (L : Leaf) (k : ℕ)
local notation "rowₖ" => L.rows.getD k ⟨1, []⟩
local notation:max "featureₖ " c:arg => (L.cols.get c).v.getD k 0
local notation:max "diagonalₖ " c:arg => (L.cols.get c).D.getD k 1
local notation:max "familyₖ " i:arg => (rowₖ).fam.get i

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
theorem near_row_of_bins {ι : Type*} [Fintype ι] (v Dg : ι → ℝ) (d τ : ℝ)
    (hDg : ∀ j, 0 < Dg j) (hd : 0 < d) (hτ0 : 0 ≤ τ) (hτd : τ ≤ Real.sqrt d)
    (hT : ∑ j, max 0 (v j - τ) ^ 2 / Dg j ≤ 1 - τ ^ 2 / d)
    (bin : ι → Option (Fin L.cols.length ⊕ Fin (rowₖ).fam.length))
    (hcol : ∀ j c, bin j = some (Sum.inl c) →
      (unscale featureₖ c ≤ v j ∨ featureₖ c ≤ 0) ∧
        Dg j ≤ unscale diagonalₖ c)
    (hfam : ∀ j i, bin j = some (Sum.inr i) →
      (unscale (familyₖ i).2.1 ≤ v j ∨
          (familyₖ i).2.1 ≤ 0) ∧
        Dg j ≤ unscale (familyₖ i).2.2 )
    (hfamD : ∀ i, 0 < (familyₖ i).2.2)
    (hn : ∀ i, ((familyₖ i).1 : ℝ) ≤
      ((univ.filter fun j => bin j = some (Sum.inr i)).card : ℝ))
    (hdrow : d ≤ unscale (rowₖ).d )
    (x : Fin L.cols.length → ℝ) (hx0 : ∀ c, 0 ≤ x c)
    (hx : ∀ c, 0 < featureₖ c →
      x c ≤ ((univ.filter fun j => bin j = some (Sum.inl c)).card : ℝ)) :
    0 ≤ τ ∧ τ ^ 2 ≤ unscale (rowₖ).d ∧
      rowLHS L x k τ ≤ 1 - τ ^ 2 / unscale (rowₖ).d := by
  let group b := univ.filter fun j => bin j = b
  let row := L.row k

  refine ⟨hτ0, ((Real.le_sqrt hτ0 hd.le).1 hτd).trans hdrow, ?_⟩
  -- the entry terms
  set t : ι → ℝ := fun j => max 0 (v j - τ) ^ 2 / Dg j

  -- (T) with the row's radius
  have hTrow : ∑ j, t j ≤ 1 - τ ^ 2 / unscale row.d := by
    refine hT.trans ?_
    gcongr
  -- split the entries by bin
  rw [← Finset.sum_fiberwise univ bin t, Fintype.sum_option, Fintype.sum_sum_type] at hTrow
  have hnone : 0 ≤ ∑ j ∈ group none , t j :=
     by bound
  -- the columns
  have hcols : ∑ c, x c * rowSlack featureₖ c τ ^ 2 /
           unscale diagonalₖ c ≤
      ∑ c, ∑ j ∈ group (some (Sum.inl c)) , t j := by
    gcongr 1 with c _
    have hcount := Finset.card_nsmul_le_sum
      (group (some (Sum.inl c))) t _ fun j hj => by
        obtain ⟨hv, hD⟩ := hcol j c (Finset.mem_filter.mp hj).2
        exact term_le (hv.imp_right unscale_nonpos) hτ0 (hDg j) hD
    simp only [nsmul_eq_mul] at hcount
    have hsum0 : 0 ≤ ∑ j ∈ group (some (Sum.inl c)) , t j :=
       by bound
    by_cases hv : featureₖ c ≤ 0
    · have h0 : rowSlack featureₖ c τ = 0 :=
        max_eq_left (by linarith [unscale_nonpos hv])
      rwa [h0, sq, zero_mul, mul_zero, zero_div]
    · rw [mul_div_assoc]
      rcases le_total (0 : ℝ) _ with hu | hu
      · exact (mul_le_mul_of_nonneg_right (hx c (lt_of_not_ge hv)) hu).trans hcount
      · exact (mul_nonpos_of_nonneg_of_nonpos (hx0 c) hu).trans hsum0
  -- the family terms
  have hfams : ((row.fam).map fun u =>
        (u.1 : ℝ) * rowSlack u.2.1 τ ^ 2 / unscale u.2.2 ).sum ≤
      ∑ i, ∑ j ∈ group (some (Sum.inr i)) , t j := by
    rw [← Fin.sum_univ_fun_getElem]
    gcongr 1 with i _
    have hDi := hfamD i

    rw [← List.get_eq_getElem, mul_div_assoc]
    refine (mul_le_mul_of_nonneg_right (hn i) (by norm_num [S]; positivity)).trans ?_
    simpa only [nsmul_eq_mul] using Finset.card_nsmul_le_sum
      (group (some (Sum.inr i))) t _ fun j hj => by
        grind [GradedNear.Cert.term_le, GradedNear.Cert.unscale_nonpos]
  unfold rowLHS
  linarith

end GradedNear.Cert
