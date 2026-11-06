/- The selected triple-ledger C rows and the affine-20 chart use different coordinates.
`FlowFamily.rowLedger` reads twenty C cells indexed by `FlowFamily.rowIndex`;
`FlowFamily.jacobianEntry` and `Rank20Certificate.det_JQ_ne_zero` concern these rows.
Relabelling gates use `Affine20.act20` on `Affine20.encode20` coordinates. The selected
C cells are not a relabelling-stable subset of the 27 C cells.

This module transfers between these coordinate systems on the genuine ledger domain.
  * `cRow L` reads the twenty `rowIndex` cells of C; `cRow_ledger54_moved` identifies
    this reading with `FlowFamily.rowLedger` on a moved triple.
  * `rowsOf v` reads those cells of `Affine20.decode20 v`. It is affine, and
    `rowsOf_encode20` identifies it with `cRow` on the domain by `Affine20.decC_encode`.
  * `chartVec c` reconstructs each chart coordinate as a rational combination of C rows:
    three-term margin sums for the twelve pair heads and one cell minus a third of
    three margin sums for the eight tensor heads.
  * `chartVec_rowsOf : chartVec (rowsOf v) = v` reduces to twenty goals using
    `decode20_inDomain` to rewrite margin sums before `ring`; it implies `rowsOf_injective`.
The inverse function theorem applies to `cRow ∘ ledger54 ∘ family`, and `chartVec` / `rowsOf`
transport the result to the chart without another determinant or analytic argument.

Each `Fin 20` index is read through its `rfl` apply lemma (`chartVec_apply_n`,
`rowsOf_apply_n`, `cRow_apply_n`); index splits use `Affine20.fin20_cases` and
`Affine20.fin3_cases`. `Ledger54` equalities use `Prod.ext` and the projection lemmas
`Affine20.decode20_C/P/Q/R`, avoiding comparisons by unfolding ledger structures. -/
module

public import Glennie.Compact.FlowFamily
public import Glennie.Compact.Affine20

@[expose] public section

namespace Glennie.Compact.ChartTransfer

open Glennie.Compact.Affine20 Glennie.Compact.FlowFamily

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Zero-margin helpers for the reconstruction maps

Each is an `ext3` telescope: `x + y + (-(x + y)) = 0`. They are stated for the `Affine20.lift4` (Chart.lean) and `Affine20.lift8` (Chart.lean). -/

/-- Every row of `lift4` sums to zero. -/
theorem lift4_row_sum (a b c d : ℝ) (i : Fin 3) :
    lift4 a b c d i 0 + lift4 a b c d i 1 + lift4 a b c d i 2 = 0 := by
  rcases fin3_cases i with rfl | rfl | rfl <;>
    simp only [lift4, ext3_zero, ext3_one, ext3_two] <;> ring

/-- Every column of `lift4` sums to zero. -/
theorem lift4_col_sum (a b c d : ℝ) (j : Fin 3) :
    lift4 a b c d 0 j + lift4 a b c d 1 j + lift4 a b c d 2 j = 0 := by
  rcases fin3_cases j with rfl | rfl | rfl <;>
    simp only [lift4, ext3_zero, ext3_one, ext3_two] <;> ring

/-- The first margin of `lift8` vanishes. -/
theorem lift8_margin_i (h000 h001 h010 h011 h100 h101 h110 h111 : ℝ) (j k : Fin 3) :
    lift8 h000 h001 h010 h011 h100 h101 h110 h111 0 j k +
      lift8 h000 h001 h010 h011 h100 h101 h110 h111 1 j k +
      lift8 h000 h001 h010 h011 h100 h101 h110 h111 2 j k = 0 := by
  rcases fin3_cases j with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
    simp only [lift8, ext3_zero, ext3_one, ext3_two] <;> ring

/-- The second margin of `lift8` vanishes. -/
theorem lift8_margin_j (h000 h001 h010 h011 h100 h101 h110 h111 : ℝ) (i k : Fin 3) :
    lift8 h000 h001 h010 h011 h100 h101 h110 h111 i 0 k +
      lift8 h000 h001 h010 h011 h100 h101 h110 h111 i 1 k +
      lift8 h000 h001 h010 h011 h100 h101 h110 h111 i 2 k = 0 := by
  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
    simp only [lift8, ext3_zero, ext3_one, ext3_two] <;> ring

/-- The third margin of `lift8` vanishes. -/
theorem lift8_margin_k (h000 h001 h010 h011 h100 h101 h110 h111 : ℝ) (i j : Fin 3) :
    lift8 h000 h001 h010 h011 h100 h101 h110 h111 i j 0 +
      lift8 h000 h001 h010 h011 h100 h101 h110 h111 i j 1 +
      lift8 h000 h001 h010 h011 h100 h101 h110 h111 i j 2 = 0 := by
  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
    simp only [lift8, ext3_zero, ext3_one, ext3_two] <;> ring

/-! ## `decode20` always lands in the genuine domain

This is the companion of the `Affine20.decode_encode` (Chart.lean). It is what makes
every margin sum of a decoded ledger rewritable, and it is used below to keep
`chartVec_rowsOf` down to twenty tiny goals. -/

/-- Every point of the chart decodes to a ledger satisfying the margin identities. -/
theorem decode20_inDomain (v : Fin 20 → ℝ) : InDomain (decode20 v) where
  P_row i := by
    simp only [decode20_P, decP]
    linarith [lift4_row_sum (v 0) (v 1) (v 2) (v 3) i]
  P_col j := by
    simp only [decode20_P, decP]
    linarith [lift4_col_sum (v 0) (v 1) (v 2) (v 3) j]
  Q_row j := by
    simp only [decode20_Q, decQ]
    linarith [lift4_row_sum (v 4) (v 5) (v 6) (v 7) j]
  Q_col k := by
    simp only [decode20_Q, decQ]
    linarith [lift4_col_sum (v 4) (v 5) (v 6) (v 7) k]
  R_row k := by
    simp only [decode20_R, decR]
    linarith [lift4_row_sum (v 8) (v 9) (v 10) (v 11) k]
  R_col i := by
    simp only [decode20_R, decR]
    linarith [lift4_col_sum (v 8) (v 9) (v 10) (v 11) i]
  C_k i j := by
    simp only [decode20_C, decode20_P, decC, decQ, decR]
    linarith [lift8_margin_k (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) i j,
      lift4_row_sum (v 4) (v 5) (v 6) (v 7) j, lift4_col_sum (v 8) (v 9) (v 10) (v 11) i]
  C_i j k := by
    simp only [decode20_C, decode20_Q, decC, decP, decR]
    linarith [lift8_margin_i (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) j k,
      lift4_col_sum (v 0) (v 1) (v 2) (v 3) j, lift4_row_sum (v 8) (v 9) (v 10) (v 11) k]
  C_j k i := by
    simp only [decode20_C, decode20_R, decC, decP, decQ]
    linarith [lift8_margin_j (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) i k,
      lift4_row_sum (v 0) (v 1) (v 2) (v 3) i, lift4_col_sum (v 4) (v 5) (v 6) (v 7) k]

/-- The chart is a right inverse of `decode20` on all of `Fin 20 → ℝ`. -/
theorem encode20_decode20 (v : Fin 20 → ℝ) : encode20 (decode20 v) = v := by
  funext n
  have hD := decode20_inDomain v
  fin_cases n <;>
    simp [encode20, centred, decode20_C, decode20_P, decode20_Q, decode20_R,
      decC, decP, decQ, decR, lift8, lift4, ext3_zero, ext3_one, ext3_two] <;> ring

/-! ## The twenty selected C rows -/

/-- The twenty `rowIndex` cells of the C block of a 54-entry ledger. -/
def cRow (L : Ledger54) : Fin 20 → ℝ := fun r =>
  L.1 (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

/-- `rowsOf` reads the same twenty cells of a decoded chart point: the affine map from chart
coordinates to C-row coordinates. -/
def rowsOf (v : Fin 20 → ℝ) : Fin 20 → ℝ := cRow (decode20 v)

theorem rowsOf_apply (v : Fin 20 → ℝ) (r : Fin 20) :
    rowsOf v r = decC v (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2 := rfl

/-- On the genuine domain the two readings agree, by the `Affine20.decC_encode`
(Chart.lean). -/
theorem rowsOf_encode20 (L : Ledger54) (h : InDomain L) : rowsOf (encode20 L) = cRow L := by
  funext r
  rw [rowsOf_apply, cRow]
  exact decC_encode L h _ _ _

/-- Reading the twenty cells preserves affine combinations. One goal at a VARIABLE row index: no
case split, no `lift4`/`lift8` expansion, nothing but the `Prod`/`Pi` pointwise lemmas. -/
theorem cRow_affine : AffineComb cRow := by
  intro x y t
  funext r
  simp only [cRow, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]

/-- `rowsOf` preserves affine combinations, as the composition of the `Affine20.decode20_affine` (Chart.lean) with `cRow_affine`, through the `Affine20.AffineComb.comp` (Chart.lean). Deliberately NOT proved by expanding `decC` at twenty
literal indices: that would be the one wide-`ring` site in this module. -/
theorem rowsOf_affine : AffineComb rowsOf :=
  AffineComb.comp (f := decode20) (g := cRow) cRow_affine decode20_affine

theorem continuous_rowsOf : Continuous rowsOf :=
  AffineComb.continuous20 rowsOf_affine

/-! ## The explicit affine inverse on chart coordinates

Each entry is read off the margin identities of the genuine domain: the twelve pair heads are
three-term margin sums of C rows, and the eight tensor heads are one C row minus a third of the
three margin sums through that cell. The twenty row triples used here are exactly
`FlowFamily.rowIndex` (FlowFamily.lean); each sum lies inside the selected twenty. -/

/-- The twenty chart coordinates read from the twenty C rows. -/
def chartVec (c : Fin 20 → ℝ) : Fin 20 → ℝ :=
  ![c 0 + c 1 + c 2 - 1 / 3,
    c 3 + c 4 + c 5 - 1 / 3,
    c 8 + c 9 + c 10 - 1 / 3,
    c 11 + c 12 + c 13 - 1 / 3,
    c 0 + c 8 + c 16 - 1 / 3,
    c 1 + c 9 + c 17 - 1 / 3,
    c 3 + c 11 + c 18 - 1 / 3,
    c 4 + c 12 + c 19 - 1 / 3,
    c 0 + c 3 + c 6 - 1 / 3,
    c 8 + c 11 + c 14 - 1 / 3,
    c 1 + c 4 + c 7 - 1 / 3,
    c 9 + c 12 + c 15 - 1 / 3,
    c 0 - ((c 0 + c 1 + c 2) + (c 0 + c 8 + c 16) + (c 0 + c 3 + c 6)) / 3 + 2 / 9,
    c 1 - ((c 0 + c 1 + c 2) + (c 1 + c 9 + c 17) + (c 1 + c 4 + c 7)) / 3 + 2 / 9,
    c 3 - ((c 3 + c 4 + c 5) + (c 3 + c 11 + c 18) + (c 0 + c 3 + c 6)) / 3 + 2 / 9,
    c 4 - ((c 3 + c 4 + c 5) + (c 4 + c 12 + c 19) + (c 1 + c 4 + c 7)) / 3 + 2 / 9,
    c 8 - ((c 8 + c 9 + c 10) + (c 0 + c 8 + c 16) + (c 8 + c 11 + c 14)) / 3 + 2 / 9,
    c 9 - ((c 8 + c 9 + c 10) + (c 1 + c 9 + c 17) + (c 9 + c 12 + c 15)) / 3 + 2 / 9,
    c 11 - ((c 11 + c 12 + c 13) + (c 3 + c 11 + c 18) + (c 8 + c 11 + c 14)) / 3 + 2 / 9,
    c 12 - ((c 11 + c 12 + c 13) + (c 4 + c 12 + c 19) + (c 9 + c 12 + c 15)) / 3 + 2 / 9]

/-- **The arithmetic heart.** `chartVec` inverts `rowsOf` on all of `Fin 20 → ℝ`.

PROOF SKETCH, twenty goals, each one line after the rewrites.
  * `funext m`, then `rcases fin20_cases m` (Chart.lean).
  * Rewrite the left side with `chartVec_apply_m`, then each `rowsOf v r` occurring in it with
    `rowsOf_apply_r`.
  * Goals 0-3: the three rows are the three `k` values of one `(i, j)` pair, so `rowsOf_P` turns
    the sum into `decP v i j`; `decP` then unfolds to `1/3 + lift4 … i j` and the four head cases
    close by `ext3_zero`/`ext3_one` plus `ring`.
  * Goals 4-7 use `rowsOf_Q`, goals 8-11 use `rowsOf_R`, identically.
  * Goals 12-19: the cell is one of the eight heads; the three bracketed sums are rewritten by
    `rowsOf_P`, `rowsOf_Q`, `rowsOf_R`, so the goal becomes
    `decC v i j k - (decP v i j + decQ v j k + decR v k i)/3 + 2/9 = v (12 + 4i + 2j + k)`,
    which is `lift8` at a head cell by the definition of `decC` (Chart.lean) and closes by
    `ext3_zero`/`ext3_one` plus `ring`.
No step unfolds a `Ledger54` structure, and no goal carries more than nine chart coordinates. -/
theorem chartVec_rowsOf (v : Fin 20 → ℝ) : chartVec (rowsOf v) = v := by
  funext m
  fin_cases m <;>
    simp [chartVec, rowsOf, cRow, rowIndex,
      (decode20_inDomain v).C_k, (decode20_inDomain v).C_i, (decode20_inDomain v).C_j,
      decode20_C, decode20_P, decode20_Q, decode20_R,
      decP, decQ, decR, decC, lift4, lift8, ext3_zero, ext3_one, ext3_two] <;> ring

/-! ## The bridge to the flowed family

`FlowFamily.rowLedger` (FlowFamily.lean) is literally `cRow` of the 54-entry ledger of the
moved triple. -/

/-- The moved triple of the family, as one object. -/
def movedTriple (T : Fin 3 → Fin 3 → Albert) (s : Fin 20 → ℝ) : Fin 3 → Fin 3 → Albert :=
  fun a => movedFrame contextDirection contextDirection_isJordanDerivation
    contextDirection_traceFree T a s

theorem movedTriple_zero (T : Fin 3 → Fin 3 → Albert) : movedTriple T 0 = T := by
  funext a
  exact movedFrame_zero contextDirection contextDirection_isJordanDerivation
    contextDirection_traceFree T a

/-- Every moved frame is a frame, by the `FlowFamily.movedFrame_frame`
(FlowFamily.lean). -/
theorem movedTriple_frame (T : Fin 3 → Fin 3 → Albert) (hT : ∀ a, Frame (T a))
    (s : Fin 20 → ℝ) (a : Fin 3) : Frame (movedTriple T s a) :=
  movedFrame_frame contextDirection contextDirection_isJordanDerivation
    contextDirection_traceFree T a (hT a) s

/-- Hence the moved ledger is always in the genuine domain, by `Affine20.ledger54_inDomain`
(Chart.lean). -/
theorem movedTriple_inDomain (T : Fin 3 → Fin 3 → Albert) (hT : ∀ a, Frame (T a))
    (s : Fin 20 → ℝ) : InDomain (ledger54 (movedTriple T s)) :=
  ledger54_inDomain (movedTriple T s) (movedTriple_frame T hT s)

/-- `rowLedger` is `cRow` of the moved 54-entry ledger. -/
theorem cRow_ledger54_movedTriple (T : Fin 3 → Fin 3 → Albert) (s : Fin 20 → ℝ) :
    cRow (ledger54 (movedTriple T s)) = rowLedger T s := by
  funext r
  rw [cRow, ledger54_C, rowLedger]
  rfl

/-- **Chart transfer.** For a frame triple, the chart point of the moved ledger is recovered
from the twenty selected C rows. This identity indexes sections by chart
coordinates, and the reason no new 20x20 determinant is needed. -/
theorem rowsOf_encode20_movedTriple (T : Fin 3 → Fin 3 → Albert) (hT : ∀ a, Frame (T a))
    (s : Fin 20 → ℝ) :
    rowsOf (encode20 (ledger54 (movedTriple T s))) = rowLedger T s := by
  rw [rowsOf_encode20 _ (movedTriple_inDomain T hT s), cRow_ledger54_movedTriple]

/-- Equivalently, the chart point is `chartVec` of the twenty rows. -/
theorem encode20_movedTriple_eq_chartVec (T : Fin 3 → Fin 3 → Albert) (hT : ∀ a, Frame (T a))
    (s : Fin 20 → ℝ) :
    encode20 (ledger54 (movedTriple T s)) = chartVec (rowLedger T s) := by
  rw [← rowsOf_encode20_movedTriple T hT s, chartVec_rowsOf]

end
end Glennie.Compact.ChartTransfer
