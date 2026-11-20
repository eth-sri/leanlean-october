module

public import GradedNear.Cert.Access

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

/-- Charge a single bin to the entries assigned to it. A column has nonnegative
weight, whereas a family is known to have positive diagonal. -/
private lemma charge {ι : Type*} (B : Finset ι) {v D : ι → ℝ} {w d : ℤ} {x τ : ℝ}
    (hD : ∀ j, 0 < D j) (ht : 0 ≤ τ) (hn : 0 ≤ x ∨ 0 < d)
    (hx : 0 < w → x ≤ B.card) (h : ∀ j ∈ B, (scaled w ≤ v j ∨ w ≤ 0) ∧ D j ≤ scaled d) :
    x * (max 0 (scaled w - τ))^2 / scaled d ≤ ∑ j ∈ B, (max 0 (v j - τ))^2 / D j := by
  have hS : (0:ℝ) < S := by norm_num [S]
  have hnn := sum_nonneg (s := B) fun j _ => div_nonneg (sq_nonneg (max 0 (v j - τ))) (hD j).le
  by_cases hv : 0 < w
  · rw [mul_div_assoc]
    by_cases hd : 0 ≤ scaled d
    · grw [hx hv]; rw [← nsmul_eq_mul, ← sum_const]
      refine sum_le_sum fun j hj => ?_
      obtain ⟨hw, hd'⟩ := h j hj
      bound
    · 
      exact (mul_nonpos_of_nonneg_of_nonpos (hn.resolve_right fun hh => hd (by positivity)) (div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_ge hd))).trans hnn
  · have : scaled w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by aesop) hS.le
    simpa [max_eq_left (show scaled w - τ ≤ 0 by linarith)] using hnn

variable (L : Leaf) (k : ℕ)
local notation "rₖ" => rowAt L k
local notation "fₖ " i:arg => List.get (RowHead.fam rₖ) i
local notation "vₖ " c:arg => featureAt (L.cols.get c) k
local notation "Dₖ " c:arg => diagonalAt (L.cols.get c) k

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
    (hT : ∑ j, (max 0 (v j - τ)) ^ 2 / Dg j ≤ 1 - τ ^ 2 / d)
    (bin : ι → Option (Fin L.cols.length ⊕ Fin (rₖ).fam.length))
    (hcol : ∀ j c, bin j = some (Sum.inl c) →
      (inUnits (vₖ c) ≤ v j ∨ vₖ c ≤ 0) ∧
        Dg j ≤ inUnits (Dₖ c))
    (hfam : ∀ j i, bin j = some (Sum.inr i) →
      (inUnits (fₖ i).2.1 ≤ v j ∨
          (fₖ i).2.1 ≤ 0) ∧
        Dg j ≤ inUnits (fₖ i).2.2)
    (hfamD : ∀ i, 0 < (fₖ i).2.2)
    (hn : ∀ i, ((fₖ i).1 : ℝ) ≤
      ((univ.filter fun j => bin j = some (Sum.inr i)).card : ℝ))
    (hdrow : d ≤ inUnits (rₖ).d)
    (x : Fin L.cols.length → ℝ) (hx0 : ∀ c, 0 ≤ x c)
    (hx : ∀ c, 0 < vₖ c →
      x c ≤ ((univ.filter fun j => bin j = some (Sum.inl c)).card : ℝ)) :
    0 ≤ τ ∧ τ ^ 2 ≤ inUnits (rₖ).d ∧
      rowLHS L x k τ ≤ 1 - τ ^ 2 / inUnits (rₖ).d := by
  refine ⟨hτ0, ((Real.le_sqrt hτ0 hd.le).mp hτd).trans hdrow, ?_⟩
  let t j := (max 0 (v j - τ))^2 / Dg j
  let mass b := ∑ j ∈ univ.filter (fun j => bin j = some b), t j
  calc _ ≤ (∑ c, mass (.inl c)) + ∑ i, mass (.inr i) := by
         apply add_le_add (sum_le_sum fun c _ => charge _ hDg hτ0 (.inl (hx0 c)) (hx c)
           fun j hj => hcol j c (mem_filter.mp hj).2)
         rw [← Fin.sum_univ_fun_getElem]
         exact sum_le_sum fun i _ => charge _ hDg hτ0 (.inr (hfamD i)) (fun _ => hn i)
           fun j hj => hfam j i (mem_filter.mp hj).2
       _ ≤ ∑ j, t j := by
         rw [← sum_fiberwise univ bin t, Fintype.sum_option, Fintype.sum_sum_type]
         exact le_add_of_nonneg_left (sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hDg j).le)
       _ ≤ _ := hT.trans (by gcongr)

end GradedNear.Cert
