module

public import Glennie.Compact.FlowFamily
public import Glennie.Compact.Affine20
public import Glennie.Compact.Rank20Reduction
public import Glennie.Compact.FlatBase
public import Glennie.Compactness
public import Glennie.BasicLaws
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Order.OrderClosed

@[expose] public section

namespace Glennie.Compact.Sections

open Glennie.Compact.Affine20 Glennie.Compact.NativeDictionary Glennie.Compact.FlowFamily
  Glennie.Compact.FlatBase Glennie.Compact.Rank20 Glennie.Compact.Rank20Certificate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false

def cRow (L : Ledger54) : Fin 20 → ℝ := fun r =>
  L.1 (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

def rowsOf (v : Fin 20 → ℝ) : Fin 20 → ℝ := cRow (decode20 v)

theorem rowsOf_encode20 (L : Ledger54) (h : InDomain L) : rowsOf (encode20 L) = cRow L := by
  funext r; exact decC_encode L h _ _ _

theorem cRow_affine : AffineComb cRow := fun x y t => by
  funext r
  simp only [cRow, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]

theorem rowsOf_affine : AffineComb rowsOf :=
  AffineComb.comp (f := decode20) (g := cRow) cRow_affine decode20_affine

theorem continuous_rowsOf : Continuous rowsOf :=
  AffineComb.continuous20 rowsOf_affine

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

theorem lift4_row_sum (a b c d : ℝ) (i : Fin 3) :
    lift4 a b c d i 0 + lift4 a b c d i 1 + lift4 a b c d i 2 = 0 := by
  rcases fin3_cases i with rfl | rfl | rfl <;>
    simp only [lift4, ext3_zero, ext3_one, ext3_two] <;> ring

theorem lift4_col_sum (a b c d : ℝ) (j : Fin 3) :
    lift4 a b c d 0 j + lift4 a b c d 1 j + lift4 a b c d 2 j = 0 := by
  simp only [lift4, ext3_zero, ext3_one, ext3_two]; ring

theorem lift8_margin_i (h000 h001 h010 h011 h100 h101 h110 h111 : ℝ) (j k : Fin 3) :
    lift8 h000 h001 h010 h011 h100 h101 h110 h111 0 j k +
      lift8 h000 h001 h010 h011 h100 h101 h110 h111 1 j k +
      lift8 h000 h001 h010 h011 h100 h101 h110 h111 2 j k = 0 := by
  simp only [lift8, ext3_zero, ext3_one, ext3_two]; ring

theorem lift8_margin_j (h000 h001 h010 h011 h100 h101 h110 h111 : ℝ) (i k : Fin 3) :
    lift8 h000 h001 h010 h011 h100 h101 h110 h111 i 0 k +
      lift8 h000 h001 h010 h011 h100 h101 h110 h111 i 1 k +
      lift8 h000 h001 h010 h011 h100 h101 h110 h111 i 2 k = 0 := by
  rcases fin3_cases i with rfl | rfl | rfl <;>
    simp only [lift8, ext3_zero, ext3_one, ext3_two] <;> ring

theorem lift8_margin_k (h000 h001 h010 h011 h100 h101 h110 h111 : ℝ) (i j : Fin 3) :
    lift8 h000 h001 h010 h011 h100 h101 h110 h111 i j 0 +
      lift8 h000 h001 h010 h011 h100 h101 h110 h111 i j 1 +
      lift8 h000 h001 h010 h011 h100 h101 h110 h111 i j 2 = 0 := by
  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
    simp only [lift8, ext3_zero, ext3_one, ext3_two] <;> ring

theorem decode20_inDomain (v : Fin 20 → ℝ) : InDomain (decode20 v) where
  P_row i := by simp only [decode20_P, decP]; linarith [lift4_row_sum (v 0) (v 1) (v 2) (v 3) i]
  P_col j := by simp only [decode20_P, decP]; linarith [lift4_col_sum (v 0) (v 1) (v 2) (v 3) j]
  Q_row j := by simp only [decode20_Q, decQ]; linarith [lift4_row_sum (v 4) (v 5) (v 6) (v 7) j]
  Q_col k := by simp only [decode20_Q, decQ]; linarith [lift4_col_sum (v 4) (v 5) (v 6) (v 7) k]
  R_row k := by simp only [decode20_R, decR]; linarith [lift4_row_sum (v 8) (v 9) (v 10) (v 11) k]
  R_col i := by simp only [decode20_R, decR]; linarith [lift4_col_sum (v 8) (v 9) (v 10) (v 11) i]
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

theorem rowsOf_apply (v : Fin 20 → ℝ) (r : Fin 20) :
    rowsOf v r = decC v (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2 := rfl

private theorem encode20_eq (L : Ledger54) :
    encode20 L 0 = L.2.1 0 0 - 1 / 3 ∧ encode20 L 1 = L.2.1 0 1 - 1 / 3 ∧
    encode20 L 2 = L.2.1 1 0 - 1 / 3 ∧ encode20 L 3 = L.2.1 1 1 - 1 / 3 ∧
    encode20 L 4 = L.2.2.1 0 0 - 1 / 3 ∧ encode20 L 5 = L.2.2.1 0 1 - 1 / 3 ∧
    encode20 L 6 = L.2.2.1 1 0 - 1 / 3 ∧ encode20 L 7 = L.2.2.1 1 1 - 1 / 3 ∧
    encode20 L 8 = L.2.2.2 0 0 - 1 / 3 ∧ encode20 L 9 = L.2.2.2 0 1 - 1 / 3 ∧
    encode20 L 10 = L.2.2.2 1 0 - 1 / 3 ∧ encode20 L 11 = L.2.2.2 1 1 - 1 / 3 ∧
    encode20 L 12 = centred L 0 0 0 ∧ encode20 L 13 = centred L 0 0 1 ∧
    encode20 L 14 = centred L 0 1 0 ∧ encode20 L 15 = centred L 0 1 1 ∧
    encode20 L 16 = centred L 1 0 0 ∧ encode20 L 17 = centred L 1 0 1 ∧
    encode20 L 18 = centred L 1 1 0 ∧ encode20 L 19 = centred L 1 1 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem encode20_decode20 (v : Fin 20 → ℝ) : encode20 (decode20 v) = v := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9,
    e10, e11, e12, e13, e14, e15, e16, e17, e18, e19⟩ := encode20_eq (decode20 v)
  funext n
  rcases fin20_cases n with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> {
    simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18,
      e19, centred, decode20_C, decode20_P, decode20_Q, decode20_R, decC, decP, decQ, decR, lift8,
      lift4, ext3_zero, ext3_one]
    ring }

private theorem rowsOf_eq (v : Fin 20 → ℝ) :
    rowsOf v 0 = decC v 0 0 0 ∧ rowsOf v 1 = decC v 0 0 1 ∧ rowsOf v 2 = decC v 0 0 2 ∧
    rowsOf v 3 = decC v 0 1 0 ∧ rowsOf v 4 = decC v 0 1 1 ∧ rowsOf v 5 = decC v 0 1 2 ∧
    rowsOf v 6 = decC v 0 2 0 ∧ rowsOf v 7 = decC v 0 2 1 ∧ rowsOf v 8 = decC v 1 0 0 ∧
    rowsOf v 9 = decC v 1 0 1 ∧ rowsOf v 10 = decC v 1 0 2 ∧ rowsOf v 11 = decC v 1 1 0 ∧
    rowsOf v 12 = decC v 1 1 1 ∧ rowsOf v 13 = decC v 1 1 2 ∧ rowsOf v 14 = decC v 1 2 0 ∧
    rowsOf v 15 = decC v 1 2 1 ∧ rowsOf v 16 = decC v 2 0 0 ∧ rowsOf v 17 = decC v 2 0 1 ∧
    rowsOf v 18 = decC v 2 1 0 ∧ rowsOf v 19 = decC v 2 1 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem chartVec_eq (c : Fin 20 → ℝ) :
    chartVec c 0 = c 0 + c 1 + c 2 - 1 / 3 ∧
    chartVec c 1 = c 3 + c 4 + c 5 - 1 / 3 ∧
    chartVec c 2 = c 8 + c 9 + c 10 - 1 / 3 ∧
    chartVec c 3 = c 11 + c 12 + c 13 - 1 / 3 ∧
    chartVec c 4 = c 0 + c 8 + c 16 - 1 / 3 ∧
    chartVec c 5 = c 1 + c 9 + c 17 - 1 / 3 ∧
    chartVec c 6 = c 3 + c 11 + c 18 - 1 / 3 ∧
    chartVec c 7 = c 4 + c 12 + c 19 - 1 / 3 ∧
    chartVec c 8 = c 0 + c 3 + c 6 - 1 / 3 ∧
    chartVec c 9 = c 8 + c 11 + c 14 - 1 / 3 ∧
    chartVec c 10 = c 1 + c 4 + c 7 - 1 / 3 ∧
    chartVec c 11 = c 9 + c 12 + c 15 - 1 / 3 ∧
    chartVec c 12 = c 0 - ((c 0 + c 1 + c 2) + (c 0 + c 8 + c 16) + (c 0 + c 3 + c 6)) / 3 + 2 / 9 ∧
    chartVec c 13 = c 1 - ((c 0 + c 1 + c 2) + (c 1 + c 9 + c 17) + (c 1 + c 4 + c 7)) / 3 + 2 / 9 ∧
    chartVec c 14 = c 3 - ((c 3 + c 4 + c 5) + (c 3 + c 11 + c 18) + (c 0 + c 3 + c 6)) / 3 + 2 / 9 ∧
    chartVec c 15 = c 4 - ((c 3 + c 4 + c 5) + (c 4 + c 12 + c 19) + (c 1 + c 4 + c 7)) / 3 + 2 / 9 ∧
    chartVec c 16 = c 8 - ((c 8 + c 9 + c 10) + (c 0 + c 8 + c 16) + (c 8 + c 11 + c 14)) / 3 + 2 / 9 ∧
    chartVec c 17 = c 9 - ((c 8 + c 9 + c 10) + (c 1 + c 9 + c 17) + (c 9 + c 12 + c 15)) / 3 + 2 / 9 ∧
    chartVec c 18 = c 11 - ((c 11 + c 12 + c 13) + (c 3 + c 11 + c 18) + (c 8 + c 11 + c 14)) / 3 + 2 / 9 ∧
    chartVec c 19 = c 12 - ((c 11 + c 12 + c 13) + (c 4 + c 12 + c 19) + (c 9 + c 12 + c 15)) / 3 + 2 / 9 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem chartVec_rowsOf (v : Fin 20 → ℝ) : chartVec (rowsOf v) = v := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9,
    r10, r11, r12, r13, r14, r15, r16, r17, r18, r19⟩ := rowsOf_eq v
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9,
    c10, c11, c12, c13, c14, c15, c16, c17, c18, c19⟩ := chartVec_eq (rowsOf v)
  have hP := fun i j => (decode20_inDomain v).C_k i j
  have hQ := fun j k => (decode20_inDomain v).C_i j k
  have hR := fun k i => (decode20_inDomain v).C_j k i
  simp only [decode20_C, decode20_P, decode20_Q, decode20_R] at hP hQ hR
  funext m
  rcases fin20_cases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> {
    simp only [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
      r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19]
    simp only [hP, hQ, hR]
    simp only [decC, decP, decQ, decR, lift8, lift4, ext3_zero, ext3_one]
    ring }

def movedTriple (T : Fin 3 → Fin 3 → Albert) (s : Fin 20 → ℝ) : Fin 3 → Fin 3 → Albert :=
  fun a => movedFrame contextDirection contextDirection_isJordanDerivation
    contextDirection_traceFree T a s

theorem movedTriple_zero (T : Fin 3 → Fin 3 → Albert) : movedTriple T 0 = T :=
  funext fun a => movedFrame_zero contextDirection contextDirection_isJordanDerivation
    contextDirection_traceFree T a

theorem movedTriple_frame (T : Fin 3 → Fin 3 → Albert) (hT : ∀ a, Frame (T a))
    (s : Fin 20 → ℝ) (a : Fin 3) : Frame (movedTriple T s a) :=
  movedFrame_frame contextDirection contextDirection_isJordanDerivation
    contextDirection_traceFree T a (hT a) s

theorem cRow_ledger54_movedTriple (T : Fin 3 → Fin 3 → Albert) (s : Fin 20 → ℝ) :
    cRow (ledger54 (movedTriple T s)) = rowLedger T s := by
  funext r; rw [cRow, ledger54_C, rowLedger]; rfl

theorem rowsOf_encode20_movedTriple (T : Fin 3 → Fin 3 → Albert) (hT : ∀ a, Frame (T a))
    (s : Fin 20 → ℝ) :
    rowsOf (encode20 (ledger54 (movedTriple T s))) = rowLedger T s := by
  rw [rowsOf_encode20 _ (ledger54_inDomain (movedTriple T s) (movedTriple_frame T hT s)),
    cRow_ledger54_movedTriple]

theorem encode20_movedTriple_eq_chartVec (T : Fin 3 → Fin 3 → Albert) (hT : ∀ a, Frame (T a))
    (s : Fin 20 → ℝ) :
    encode20 (ledger54 (movedTriple T s)) = chartVec (rowLedger T s) := by
  rw [← rowsOf_encode20_movedTriple T hT s, chartVec_rowsOf]

theorem swap02_zero : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := Equiv.swap_apply_left 0 2
theorem swap02_one : (Equiv.swap (0 : Fin 3) 2) 1 = 1 :=
  Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
theorem swap02_two : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := Equiv.swap_apply_right 0 2

def revTriple (T : Triple) : Triple :=
  ![fun i => T 0 (Equiv.swap (0 : Fin 3) 2 i), T 1, T 2]

theorem revTriple_zero (T : Triple) :
    revTriple T 0 = fun i => T 0 (Equiv.swap (0 : Fin 3) 2 i) := rfl
theorem revTriple_one (T : Triple) : revTriple T 1 = T 1 := rfl
theorem revTriple_two (T : Triple) : revTriple T 2 = T 2 := rfl

def revLedger (L : Ledger54) : Ledger54 :=
  (fun i j k => L.1 (Equiv.swap (0 : Fin 3) 2 i) j k,
    fun i j => L.2.1 (Equiv.swap (0 : Fin 3) 2 i) j,
    L.2.2.1,
    fun k i => L.2.2.2 k (Equiv.swap (0 : Fin 3) 2 i))

theorem revLedger_C (L : Ledger54) (i j k : Fin 3) :
    (revLedger L).1 i j k = L.1 (Equiv.swap (0 : Fin 3) 2 i) j k := rfl
theorem revLedger_P (L : Ledger54) (i j : Fin 3) :
    (revLedger L).2.1 i j = L.2.1 (Equiv.swap (0 : Fin 3) 2 i) j := rfl
theorem revLedger_Q (L : Ledger54) (j k : Fin 3) :
    (revLedger L).2.2.1 j k = L.2.2.1 j k := rfl
theorem revLedger_R (L : Ledger54) (k i : Fin 3) :
    (revLedger L).2.2.2 k i = L.2.2.2 k (Equiv.swap (0 : Fin 3) 2 i) := rfl

theorem ledger54_revTriple (T : Triple) :
    ledger54 (revTriple T) = revLedger (ledger54 T) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    show trace (jordan (jordan (T 0 (Equiv.swap (0 : Fin 3) 2 i)) (T 1 j)) (T 2 k)) =
      trace (jordan (jordan (T 0 (Equiv.swap (0 : Fin 3) 2 i)) (T 1 j)) (T 2 k))
    rfl
  · funext i j
    show inner (T 0 (Equiv.swap (0 : Fin 3) 2 i)) (T 1 j) =
      inner (T 0 (Equiv.swap (0 : Fin 3) 2 i)) (T 1 j)
    rfl
  · funext j k
    show inner (T 1 j) (T 2 k) = inner (T 1 j) (T 2 k)
    rfl
  · funext k i
    show inner (T 2 k) (T 0 (Equiv.swap (0 : Fin 3) 2 i)) =
      inner (T 2 k) (T 0 (Equiv.swap (0 : Fin 3) 2 i))
    rfl

theorem revLedger_revLedger (L : Ledger54) : revLedger (revLedger L) = L := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl ?_))
  · funext i j k
    show L.1 (Equiv.swap (0 : Fin 3) 2 (Equiv.swap (0 : Fin 3) 2 i)) j k = L.1 i j k
    rw [Equiv.swap_apply_self]
  · funext i j
    show L.2.1 (Equiv.swap (0 : Fin 3) 2 (Equiv.swap (0 : Fin 3) 2 i)) j = L.2.1 i j
    rw [Equiv.swap_apply_self]
  · funext k i
    show L.2.2.2 k (Equiv.swap (0 : Fin 3) 2 (Equiv.swap (0 : Fin 3) 2 i)) = L.2.2.2 k i
    rw [Equiv.swap_apply_self]

theorem revLedger_inDomain {L : Ledger54} (hL : InDomain L) : InDomain (revLedger L) where
  P_row i := by simp only [revLedger_P]; exact hL.P_row (Equiv.swap (0 : Fin 3) 2 i)
  P_col j := by simp only [revLedger_P, swap02_zero, swap02_one, swap02_two]; linarith [hL.P_col j]
  Q_row j := by simp only [revLedger_Q]; exact hL.Q_row j
  Q_col k := by simp only [revLedger_Q]; exact hL.Q_col k
  R_row k := by simp only [revLedger_R, swap02_zero, swap02_one, swap02_two]; linarith [hL.R_row k]
  R_col i := by simp only [revLedger_R]; exact hL.R_col (Equiv.swap (0 : Fin 3) 2 i)
  C_k i j := by simp only [revLedger_C, revLedger_P]; exact hL.C_k (Equiv.swap (0 : Fin 3) 2 i) j
  C_i j k := by simp only [revLedger_C, revLedger_Q, swap02_zero, swap02_one, swap02_two]; linarith [hL.C_i j k]
  C_j k i := by simp only [revLedger_C, revLedger_R]; exact hL.C_j k (Equiv.swap (0 : Fin 3) 2 i)

theorem revLedger_affine : AffineComb revLedger := fun x y t => by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    simp only [revLedger_C, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · funext i j
    simp only [revLedger_P, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · funext j k
    simp only [revLedger_Q, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · funext k i
    simp only [revLedger_R, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

def tau (b : Fin 20 → ℝ) : Fin 20 → ℝ := encode20 (revLedger (decode20 b))

theorem tau_encode20 (L : Ledger54) (hL : InDomain L) :
    tau (encode20 L) = encode20 (revLedger L) := by
  rw [tau, decode_encode L hL]

theorem tau_tau (b : Fin 20 → ℝ) : tau (tau b) = b := by
  change tau (encode20 (revLedger (decode20 b))) = b
  rw [tau_encode20 _ (revLedger_inDomain (decode20_inDomain b)),
    revLedger_revLedger, encode20_decode20]

theorem continuous_tau : Continuous tau :=
  AffineComb.continuous20 (AffineComb.comp (f := decode20) (g := fun L => encode20 (revLedger L))
    (AffineComb.comp (f := revLedger) (g := encode20) encode20_affine revLedger_affine)
    decode20_affine)

theorem frame_swap {p : Fin 3 → Albert} (hp : Frame p) :
    Frame (fun i => p (Equiv.swap (0 : Fin 3) 2 i)) where
  trace_one i := hp.trace_one (Equiv.swap (0 : Fin 3) 2 i)
  idempotent i := hp.idempotent (Equiv.swap (0 : Fin 3) 2 i)
  orthogonal i j hij :=
    hp.orthogonal (Equiv.swap (0 : Fin 3) 2 i) (Equiv.swap (0 : Fin 3) 2 j)
      ((Equiv.swap (0 : Fin 3) 2).injective.ne hij)
  sum_unit := by
    show p (Equiv.swap (0 : Fin 3) 2 0) + p (Equiv.swap (0 : Fin 3) 2 1) +
      p (Equiv.swap (0 : Fin 3) 2 2) = 1
    rw [swap02_zero, swap02_one, swap02_two, ← hp.sum_unit]; abel

theorem frame_revTriple (T : Triple) (hT : ∀ a : Fin 3, Frame (T a)) (a : Fin 3) :
    Frame (revTriple T a) := by
  rcases fin3_cases a with rfl | rfl | rfl
  · rw [revTriple_zero]; exact frame_swap (hT 0)
  · rw [revTriple_one]; exact hT 1
  · rw [revTriple_two]; exact hT 2

def phiOf (T : Triple) : ℝ := phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2))

theorem phiOf_apply (T : Triple) :
    phiOf T = phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2)) := rfl

theorem encoder_revTriple_zero (T : Triple) :
    encoder (revTriple T 0) = -encoder (T 0) := by
  show T 0 (Equiv.swap (0 : Fin 3) 2 2) - T 0 (Equiv.swap (0 : Fin 3) 2 0) = -(T 0 2 - T 0 0)
  rw [swap02_two, swap02_zero]; abel

theorem phiOf_revTriple (T : Triple) : phiOf (revTriple T) = -phiOf T := by
  have h0 : encoder (revTriple T 0) = (-1 : ℝ) • encoder (T 0) := by
    rw [encoder_revTriple_zero, neg_one_smul]
  simp only [phiOf_apply]
  rw [h0, revTriple_one, revTriple_two, phi_smul_first]; ring

theorem negPhiOf_revTriple (T : Triple) :
    (fun X : Triple => -phiOf X) (revTriple T) = -((fun X : Triple => -phiOf X) T) := by
  show -phiOf (revTriple T) = -(-phiOf T)
  rw [phiOf_revTriple]

theorem continuous_U : Continuous fun p : Albert × Albert => U p.1 p.2 := by
  have h12 : Continuous fun p : Albert × Albert => jordan p.1 p.2 := continuous_jordan
  have hp11 : Continuous fun p : Albert × Albert => (p.1, p.1) :=
    continuous_fst.prodMk continuous_fst
  have h11 : Continuous fun p : Albert × Albert => jordan p.1 p.1 := by
    simpa only [Function.comp_def] using continuous_jordan.comp hp11
  have hp1 : Continuous fun p : Albert × Albert => (p.1, jordan p.1 p.2) :=
    continuous_fst.prodMk h12
  have h1 : Continuous fun p : Albert × Albert => jordan p.1 (jordan p.1 p.2) := by
    simpa only [Function.comp_def] using continuous_jordan.comp hp1
  have hp2 : Continuous fun p : Albert × Albert => (jordan p.1 p.1, p.2) :=
    h11.prodMk continuous_snd
  have h2 : Continuous fun p : Albert × Albert => jordan (jordan p.1 p.1) p.2 := by
    simpa only [Function.comp_def] using continuous_jordan.comp hp2
  have hU : (fun p : Albert × Albert => U p.1 p.2) =
      fun p : Albert × Albert =>
        jordan p.1 (jordan p.1 p.2) + jordan p.1 (jordan p.1 p.2) -
          jordan (jordan p.1 p.1) p.2 := by
    funext p; simp only [U, two_smul]
  rw [hU]
  exact (h1.add h1).sub h2

theorem continuous_phi3 :
    Continuous fun p : Albert × Albert × Albert => phi p.1 p.2.1 p.2.2 := by
  have cx : Continuous fun p : Albert × Albert × Albert => p.1 := continuous_fst
  have cy : Continuous fun p : Albert × Albert × Albert => p.2.1 :=
    continuous_fst.comp continuous_snd
  have cz : Continuous fun p : Albert × Albert × Albert => p.2.2 :=
    continuous_snd.comp continuous_snd
  have hpyz : Continuous fun p : Albert × Albert × Albert => (p.2.1, p.2.2) := cy.prodMk cz
  have hyz : Continuous fun p : Albert × Albert × Albert => U p.2.1 p.2.2 := by
    simpa only [Function.comp_def] using continuous_U.comp hpyz
  have hpxz : Continuous fun p : Albert × Albert × Albert => (p.1, p.2.2) := cx.prodMk cz
  have hxz : Continuous fun p : Albert × Albert × Albert => U p.1 p.2.2 := by
    simpa only [Function.comp_def] using continuous_U.comp hpxz
  have hpA : Continuous fun p : Albert × Albert × Albert => (p.1, U p.2.1 p.2.2) := cx.prodMk hyz
  have hA : Continuous fun p : Albert × Albert × Albert => U p.1 (U p.2.1 p.2.2) := by
    simpa only [Function.comp_def] using continuous_U.comp hpA
  have hpB : Continuous fun p : Albert × Albert × Albert => (p.2.1, U p.1 p.2.2) := cy.prodMk hxz
  have hB : Continuous fun p : Albert × Albert × Albert => U p.2.1 (U p.1 p.2.2) := by
    simpa only [Function.comp_def] using continuous_U.comp hpB
  have hpJ : Continuous fun p : Albert × Albert × Albert => (p.1, p.2.1) := cx.prodMk cy
  have hJ : Continuous fun p : Albert × Albert × Albert => jordan p.1 p.2.1 := by
    simpa only [Function.comp_def] using continuous_jordan.comp hpJ
  have hpC : Continuous fun p : Albert × Albert × Albert => (p.2.2, jordan p.1 p.2.1) := cz.prodMk hJ
  have hC : Continuous fun p : Albert × Albert × Albert => U p.2.2 (jordan p.1 p.2.1) := by
    simpa only [Function.comp_def] using continuous_U.comp hpC
  have hphi : (fun p : Albert × Albert × Albert => phi p.1 p.2.1 p.2.2) =
      fun p : Albert × Albert × Albert =>
        inner (U p.1 (U p.2.1 p.2.2) - U p.2.1 (U p.1 p.2.2))
          (U p.2.2 (jordan p.1 p.2.1)) := by
    funext p; simp only [phi]
  rw [hphi]
  have hpPhi : Continuous fun p : Albert × Albert × Albert =>
      (U p.1 (U p.2.1 p.2.2) - U p.2.1 (U p.1 p.2.2),
        U p.2.2 (jordan p.1 p.2.1)) := (hA.sub hB).prodMk hC
  simpa only [Function.comp_def] using continuous_native_inner.comp hpPhi

theorem continuous_encoder_slot (a : Fin 3) :
    Continuous fun T : Triple => encoder (T a) := by
  have h2 : Continuous fun T : Triple => T a 2 :=
    continuous_apply_apply (ρ := fun (_ _ : Fin 3) => Albert) a (2 : Fin 3)
  have h0 : Continuous fun T : Triple => T a 0 :=
    continuous_apply_apply (ρ := fun (_ _ : Fin 3) => Albert) a (0 : Fin 3)
  change Continuous fun T : Triple => T a 2 - T a 0
  exact h2.sub h0

theorem continuous_phiOf : Continuous phiOf := by
  have hp : Continuous fun T : Triple =>
      (encoder (T 0), encoder (T 1), encoder (T 2)) :=
    (continuous_encoder_slot 0).prodMk
      ((continuous_encoder_slot 1).prodMk (continuous_encoder_slot 2))
  change Continuous fun T : Triple => phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2))
  simpa only [Function.comp_def] using continuous_phi3.comp hp

theorem continuous_revTriple : Continuous fun T : Triple => revTriple T := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  rcases fin3_cases a with rfl | rfl | rfl
  · exact (continuous_apply (Equiv.swap (0 : Fin 3) 2 i)).comp (continuous_apply 0)
  · exact (continuous_apply i).comp (continuous_apply 1)
  · exact (continuous_apply i).comp (continuous_apply 2)

def decodeCLM : (Fin 27 → ℝ) →L[ℝ] Albert :=
  LinearMap.toContinuousLinearMap extEquiv.toLinearMap

theorem decodeCLM_apply (c : Fin 27 → ℝ) : decodeCLM c = extEquiv c := rfl

theorem continuous_movedTriple_atom (T : Triple) (a i : Fin 3) :
    Continuous fun s : Fin 20 → ℝ => movedTriple T s a i := by
  have h : Continuous fun s : Fin 20 → ℝ =>
      extEquiv.symm (movedFrame contextDirection contextDirection_isJordanDerivation
        contextDirection_traceFree T a s i) :=
    continuous_movedFrame_coord contextDirection contextDirection_isJordanDerivation
      contextDirection_traceFree T a i
  have h2 : Continuous fun s : Fin 20 → ℝ =>
      decodeCLM (extEquiv.symm (movedFrame contextDirection
        contextDirection_isJordanDerivation contextDirection_traceFree T a s i)) :=
    decodeCLM.continuous.comp h
  simp only [decodeCLM_apply, LinearEquiv.apply_symm_apply] at h2
  show Continuous fun s : Fin 20 → ℝ =>
    movedFrame contextDirection contextDirection_isJordanDerivation
      contextDirection_traceFree T a s i
  exact h2

theorem exists_section_of_equiv (T : Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T) :
    ∃ W : Set (Fin 20 → ℝ), IsOpen W ∧ encode20 (ledger54 T) ∈ W ∧
      ∃ sec : (Fin 20 → ℝ) → Triple,
        ContinuousOn sec W ∧
        sec (encode20 (ledger54 T)) = T ∧
        (∀ b ∈ W, ∀ a : Fin 3, Frame (sec b a)) ∧
        (∀ b ∈ W, encode20 (ledger54 (sec b)) = b) := by
  have hd : HasStrictFDerivAt (rowLedger T) (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) 0 :=
    hasStrictFDerivAt_rowLedger_of_equiv T e he
  obtain ⟨Psi, hcoe, hsrc, htgt⟩ :
      ∃ Psi : OpenPartialHomeomorph (Fin 20 → ℝ) (Fin 20 → ℝ),
        (Psi : (Fin 20 → ℝ) → (Fin 20 → ℝ)) = rowLedger T ∧
          (0 : Fin 20 → ℝ) ∈ Psi.source ∧ rowLedger T 0 ∈ Psi.target :=
    ⟨hd.toOpenPartialHomeomorph (rowLedger T), hd.toOpenPartialHomeomorph_coe,
      hd.mem_toOpenPartialHomeomorph_source, hd.image_mem_toOpenPartialHomeomorph_target⟩
  have hb0 : rowsOf (encode20 (ledger54 T)) = rowLedger T 0 := by
    have h := rowsOf_encode20_movedTriple T hT 0; rwa [movedTriple_zero] at h
  have hleft : Psi.symm (rowLedger T 0) = 0 := by
    have h := Psi.left_inv hsrc; rwa [hcoe] at h
  have hright (b : Fin 20 → ℝ) (hb : b ∈ Psi.target) : rowLedger T (Psi.symm b) = b := by
    have h := Psi.right_inv hb; rwa [hcoe] at h
  have hsigma : ContinuousOn (fun b : Fin 20 → ℝ => Psi.symm (rowsOf b))
      (rowsOf ⁻¹' Psi.target) :=
    Psi.continuousOn_symm.comp' continuous_rowsOf.continuousOn (fun _ hb => hb)
  refine ⟨rowsOf ⁻¹' Psi.target, Psi.open_target.preimage continuous_rowsOf,
    by show rowsOf (encode20 (ledger54 T)) ∈ Psi.target; rwa [hb0],
    fun b => movedTriple T (Psi.symm (rowsOf b)),
    continuousOn_pi' fun a => continuousOn_pi' fun i =>
      (continuous_movedTriple_atom T a i).comp_continuousOn' hsigma,
    by show movedTriple T (Psi.symm (rowsOf (encode20 (ledger54 T)))) = T
       rw [hb0, hleft, movedTriple_zero],
    fun b _ a => movedTriple_frame T hT (Psi.symm (rowsOf b)) a,
    fun b hb => by
      show encode20 (ledger54 (movedTriple T (Psi.symm (rowsOf b)))) = b
      rw [encode20_movedTriple_eq_chartVec T hT, hright (rowsOf b) hb, chartVec_rowsOf]⟩

theorem exists_signed_section_of_equiv (T : Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T)
    (hneg : phiOf T < 0) :
    ∃ W : Set (Fin 20 → ℝ), IsOpen W ∧ encode20 (ledger54 T) ∈ W ∧
      ∃ sec : (Fin 20 → ℝ) → Triple,
        ContinuousOn sec W ∧
        (∀ b ∈ W, ∀ a : Fin 3, Frame (sec b a)) ∧
        (∀ b ∈ W, encode20 (ledger54 (sec b)) = b) ∧
        (∀ b ∈ W, phiOf (sec b) < 0) := by
  obtain ⟨W, hWopen, hmem, sec, hcont, hbase, hframes, hledger⟩ :=
    exists_section_of_equiv T hT e he
  have hphi : ContinuousOn (fun b : Fin 20 → ℝ => phiOf (sec b)) W :=
    continuous_phiOf.comp_continuousOn' hcont
  refine ⟨W ∩ (fun b : Fin 20 → ℝ => phiOf (sec b)) ⁻¹' Set.Iio 0,
    hphi.isOpen_inter_preimage hWopen isOpen_Iio, ⟨hmem, ?_⟩, sec,
    hcont.mono Set.inter_subset_left, ?_, ?_, ?_⟩
  · show phiOf (sec (encode20 (ledger54 T))) ∈ Set.Iio (0 : ℝ)
    rw [hbase]
    exact hneg
  · intro b hb a; exact hframes b hb.1 a
  · intro b hb; exact hledger b hb.1
  · intro b hb; exact hb.2

def flatBase : Triple := ![flatFrameP, flatFrameQ, flatFrameR]

theorem flatBase_zero : flatBase 0 = flatFrameP := rfl
theorem flatBase_one : flatBase 1 = flatFrameQ := rfl
theorem flatBase_two : flatBase 2 = flatFrameR := rfl

theorem flatBase_frames (a : Fin 3) : Frame (flatBase a) := by
  rcases fin3_cases a with rfl | rfl | rfl
  · rw [flatBase_zero]; exact flatFrameP_frame
  · rw [flatBase_one]; exact flatFrameQ_frame
  · rw [flatBase_two]; exact flatFrameR_frame

theorem phiOf_flatBase : phiOf flatBase = -4 / 27 := by
  rw [phiOf_apply, flatBase_zero, flatBase_one, flatBase_two]; exact flat_phi

theorem tau_flatChart :
    tau (encode20 (ledger54 flatBase)) = encode20 (ledger54 flatBase) := by
  rw [tau_encode20 (ledger54 flatBase) (ledger54_inDomain flatBase flatBase_frames)]
  have hp (i j : Fin 3) : inner (flatFrameP i) (flatFrameQ j) = 1 / 3 :=
    (uniform_pair_blocks flatFrameP flatFrameQ flatFrameR flatFrameP_frame
      flatFrameQ_frame flatFrameR_frame flat_uniform i j).1
  have hr (k i : Fin 3) : inner (flatFrameR k) (flatFrameP i) = 1 / 3 :=
    (uniform_pair_blocks flatFrameP flatFrameQ flatFrameR flatFrameP_frame
      flatFrameQ_frame flatFrameR_frame flat_uniform k i).2.2
  have hrev : revLedger (ledger54 flatBase) = ledger54 flatBase := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext i j k
      rw [revLedger_C, ledger54_C, ledger54_C, flatBase_zero, flatBase_one, flatBase_two,
        flat_uniform (Equiv.swap (0 : Fin 3) 2 i) j k, flat_uniform i j k]
    · funext i j
      rw [revLedger_P, ledger54_P, ledger54_P, flatBase_zero, flatBase_one,
        hp (Equiv.swap (0 : Fin 3) 2 i) j, hp i j]
    · funext j k; exact revLedger_Q (ledger54 flatBase) j k
    · funext k i
      rw [revLedger_R, ledger54_R, ledger54_R, flatBase_zero, flatBase_two,
        hr k (Equiv.swap (0 : Fin 3) 2 i), hr k i]
  rw [hrev]

section ReversalHelpers
variable {X L : Type*} [TopologicalSpace X] [TopologicalSpace L]

private def reversalDomain (tau : L → L) (U : Set L) : Set L := U ∩ tau ⁻¹' U

private def reversalSection (reverse : X → X) (tau : L → L) (positiveSection : L → X) :
    L → X := fun b => reverse (positiveSection (tau b))

omit [TopologicalSpace X] [TopologicalSpace L] in
private theorem flat_mem_reversalDomain (tau : L → L) (U : Set L)
    (flat : L) (hflat : flat ∈ U) (hfixed : tau flat = flat) :
    flat ∈ reversalDomain tau U :=
  ⟨hflat, by change tau flat ∈ U; rw [hfixed]; exact hflat⟩

omit [TopologicalSpace X] [TopologicalSpace L] in
private theorem reversalSection_negative (phi : X → ℝ) (reverse : X → X) (tau : L → L)
    (hphiReverse : ∀ x, phi (reverse x) = -phi x)
    (U : Set L) (positiveSection : L → X)
    (hpositive : ∀ b ∈ U, 0 < phi (positiveSection b)) :
    ∀ b ∈ reversalDomain tau U,
      phi (reversalSection reverse tau positiveSection b) < 0 := fun b hb => by
  change phi (reverse (positiveSection (tau b))) < 0
  rw [hphiReverse]
  exact neg_lt_zero.mpr (hpositive (tau b) hb.2)

omit [TopologicalSpace X] [TopologicalSpace L] in
private theorem reversalSection_valid (Valid : X → Prop) (reverse : X → X) (tau : L → L)
    (hvalidReverse : ∀ x, Valid x → Valid (reverse x))
    (U : Set L) (positiveSection : L → X)
    (hvalid : ∀ b ∈ U, Valid (positiveSection b)) :
    ∀ b ∈ reversalDomain tau U,
      Valid (reversalSection reverse tau positiveSection b) :=
  fun b hb => hvalidReverse _ (hvalid (tau b) hb.2)

omit [TopologicalSpace X] in
private theorem reversalDomain_isOpen (tau : L → L) (htau : Continuous tau)
    (U : Set L) (hU : IsOpen U) : IsOpen (reversalDomain tau U) :=
  hU.inter (IsOpen.preimage htau hU)

private theorem reversalSection_continuousOn (reverse : X → X) (tau : L → L)
    (hreverse : Continuous reverse) (htau : Continuous tau)
    (U : Set L) (positiveSection : L → X)
    (hsection : ContinuousOn positiveSection U) :
    ContinuousOn (reversalSection reverse tau positiveSection) (reversalDomain tau U) := by
  have hcomp : ContinuousOn (fun b => positiveSection (tau b)) (reversalDomain tau U) :=
    hsection.comp' htau.continuousOn (fun _ hb => hb.2)
  exact hreverse.comp_continuousOn' hcomp

end ReversalHelpers

theorem flat_two_sections (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv flatBase) :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (ledger54 flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (ledger54 (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (ledger54 (secNeg b)) = b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) := by
  obtain ⟨W, hWopen, hmem, sec, hcont, hframes, hledger, hsign⟩ :=
    exists_signed_section_of_equiv flatBase flatBase_frames e he
      (by rw [phiOf_flatBase]; norm_num)
  have hpos : ∀ b ∈ W, 0 < (fun X : Triple => -phiOf X) (sec b) := fun b hb => by
    show 0 < -phiOf (sec b); exact neg_pos.mpr (hsign b hb)
  refine ⟨reversalDomain tau W, reversalDomain_isOpen tau continuous_tau W hWopen,
    flat_mem_reversalDomain tau W (encode20 (ledger54 flatBase)) hmem tau_flatChart,
    reversalSection revTriple tau sec, sec,
    reversalSection_continuousOn revTriple tau continuous_revTriple continuous_tau W sec hcont,
    hcont.mono (fun _ hb => hb.1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact reversalSection_valid (fun X : Triple => ∀ a : Fin 3, Frame (X a)) revTriple tau
      (fun X hX => frame_revTriple X hX) W sec hframes
  · intro b hb; exact hframes b hb.1
  · intro b hb
    show encode20 (ledger54 (revTriple (sec (tau b)))) = b
    rw [ledger54_revTriple,
      ← tau_encode20 (ledger54 (sec (tau b)))
        (ledger54_inDomain (sec (tau b)) (hframes (tau b) hb.2)),
      hledger (tau b) hb.2, tau_tau]
  · intro b hb; exact hledger b hb.1
  · intro b hb
    have h := reversalSection_negative (fun X : Triple => -phiOf X) revTriple tau
      negPhiOf_revTriple W sec hpos b hb
    show 0 < phiOf (revTriple (sec (tau b)))
    exact neg_lt_zero.mp h
  · intro b hb; exact hsign b hb.1

end
end Glennie.Compact.Sections
