/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Lib.Rect
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Instances

/-!
# The two matrices of an instance (proof of Theorem 17)

"a ∼ (c, σ) ⟺ σ ≡ w(a,c) + ϱ, (c, σ) ∼ b ⟺ σ ≡ -w(b,c) (mod p)."

writeY(y, rbc, n, D, p, c0, len) writes the D × n matrix Y of the instances for the piece
{c0, …, c0 + len - 1} of C: the middle vertex (c, σ) is the row (c - c0) p + σ.  The n² cells from
rbc hold the residues of the weights w(b,c) mod p, that of (b, c) at place b n + c.
writeX(x, rac, n, D, p, c0, len, rho) writes the n × D matrix X for the residue rho; the cells from
rac hold the residues of the weights w(a,c), that of (a, c) at place a n + c.  In the statements and
docstrings below, c counts from 0 within the piece: the c-th member of the piece is the vertex
c0 + c.

Both clear the matrix and then run through the pairs of a vertex and a member of the piece; each
pair marks one cell with a 1.  So both are instances of one pair of loops:

* `markVal` says what a cell holds when the pairs before (u, w) have been handled, and `Marked` says
  it of the memory;
* `Ends.forRect` runs the two loops, using `cell_spec` to read a residue, form the label, and
  mark the destination;
* `getElem_yList` and `getElem_xList` identify the marks of all pairs with the matrices.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Marking cells: the pure side -/

section marks

/-- The cell i has been marked when the pairs (u', w'), w' < W, before (u, w) in lexicographic order
have been handled; the pair (u', w') marks the cell pos u' w'. -/
def CellMarked (pos : ℕ → ℕ → ℕ) (W u w i : ℕ) : Prop :=
  ∃ u' w', (u' < u ∨ (u' = u ∧ w' < w)) ∧ w' < W ∧ pos u' w' = i

open Classical in
/-- The content of the cell i when the pairs before (u, w) have been handled: 1 if it has been
marked, else 0. -/
noncomputable def markVal (pos : ℕ → ℕ → ℕ) (W u w i : ℕ) : ℤ :=
  if CellMarked pos W u w i then 1 else 0

variable {pos : ℕ → ℕ → ℕ} {W u w i : ℕ}

theorem markVal_zero : markVal pos W 0 0 i = 0 := by
  unfold markVal
  rw [if_neg]
  rintro ⟨u', w', h, -, -⟩
  omega

theorem markVal_step (hlt : w < W) :
    markVal pos W u (w + 1) i = if i = pos u w then 1 else markVal pos W u w i := by
  unfold markVal
  by_cases h : i = pos u w
  · rw [if_pos h, if_pos ⟨u, w, Or.inr ⟨rfl, by omega⟩, hlt, h.symm⟩]
  · rw [if_neg h]
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨u', w', h1, h2, h3⟩
      refine ⟨u', w', ?_, h2, h3⟩
      grind
    · rintro ⟨u', w', h1, h2, h3⟩
      exact ⟨u', w', by omega, h2, h3⟩

theorem markVal_row : markVal pos W u W i = markVal pos W (u + 1) 0 i := by
  unfold markVal
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨u', w', h1, h2, h3⟩
    exact ⟨u', w', by omega, h2, h3⟩
  · rintro ⟨u', w', h1, h2, h3⟩
    exact ⟨u', w', by omega, h2, h3⟩

/-- At the end, a cell is marked iff it is the cell of one of the pairs. -/
theorem markVal_end {U : ℕ} (q : Prop) [Decidable q] (h : q ↔ ∃ u' < U, ∃ w' < W, pos u' w' = i) :
    markVal pos W U 0 i = if q then 1 else 0 := by
  unfold markVal
  have : CellMarked pos W U 0 i ↔ q := by
    rw [h]
    constructor
    · rintro ⟨u', w', h1, h2, h3⟩
      grind
    · rintro ⟨u', h1, w', h2, h3⟩
      exact ⟨u', w', Or.inl h1, h2, h3⟩
  simp_all

end marks

/-! ## Marking cells: the memory -/

/-- The m cells from base hold the marks of the pairs before (u, w), and no other cell has
changed. -/
structure Marked (μ μ' : ℕ → ℤ) (base m : ℕ) (pos : ℕ → ℕ → ℕ) (W u w : ℕ) : Prop where
  cells : ∀ i < m, μ' (base + i) = markVal pos W u w i
  rest : SameOutside μ μ' base m

namespace Marked

variable {μ μ' : ℕ → ℤ} {base m : ℕ} {pos : ℕ → ℕ → ℕ} {U W u w : ℕ}

/-- After the clearing no pair has been handled. -/
theorem start (hzero : ∀ i < m, μ' (base + i) = 0) (hrest : SameOutside μ μ' base m) :
    Marked μ μ' base m pos W 0 0 :=
  ⟨fun i hi => by simp_all [markVal_zero], hrest⟩

/-- The pair (u, w) marks its cell. -/
theorem step (h : Marked μ μ' base m pos W u w) (hlt : w < W) (hpos : pos u w < m) :
    Marked μ (Function.update μ' (base + pos u w) 1) base m pos W u (w + 1) := by
  refine ⟨fun i hi => ?_, h.rest.update ⟨by omega, by omega⟩ _⟩
  rw [markVal_step hlt]
  split_ifs with e
  · simp_all
  · rw [Function.update_of_ne (by omega)]
    exact h.cells i hi

/-- The end of a row of pairs is the beginning of the next row. -/
theorem row (h : Marked μ μ' base m pos W u W) : Marked μ μ' base m pos W (u + 1) 0 :=
  ⟨fun i hi => by rw [← markVal_row]; exact h.cells i hi, h.rest⟩

/-- When all pairs have been handled, the cells hold the list of all marks. -/
theorem seg {l : List ℤ} (h : Marked μ μ' base m pos W U 0) (hlen : l.length = m)
    (hget : ∀ i (hi : i < l.length), l[i] = markVal pos W U 0 i) : Seg μ' base l :=
  fun i hi => by rw [hget i hi]; exact h.cells i (hlen ▸ hi)

end Marked

/-- The loop that clears a matrix: local 0 holds its address base, local t the number m of its
cells, and local c is the counter.  Afterwards the m cells hold 0, and no other cell has changed. -/
theorem clear_spec {μ : ℕ → ℤ} {l : List ℤ} {c t base m : ℕ} {Q : State → Prop}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : base + m < lim.space) (hc : 0 ≠ c) (ht : t ≠ c)
    (hbase : frame l 0 = base) (hm : frame l t = m)
    (h : ∀ μ', (∀ i < m, μ' (base + i) = 0) → SameOutside μ μ' base m →
      Q ⟨frame (setLocal l c m), μ'⟩) :
    Ends lim P d (.for c (v t) (.store (v 0 +' v c) (k 0))) ⟨frame l, μ⟩ (13 * m + 6) Q := by
  refine Ends.pass (x := t) (y := 0) (dst := base) (n := m) (fun _ => 0)
    (fun j _ => ⟨?_, by simp⟩) ?_ hw (by omega) hm hbase ht hc
  · change ((0 : ℕ) : ℤ) ≤ lim.word
    omega
  · rw [update_frame_setLocal]
    exact h _ (fun i hi => wrote_done hi) (sameOutside_wrote le_rfl)

/-! ## What both routines assume -/

/-- The residues R of the n² weights, all below p, stand at res.  The matrix has m = D n cells at
base, apart from the residues.  The piece {c0, …, c0 + len - 1} lies within the n vertices, and its
len p labels within the D middle vertices. -/
structure WritePre (lim : Limits) (μ : ℕ → ℤ) (base m res n D p c0 len : ℕ) (R : List ℕ) :
    Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  seg : SegN μ res R
  length : R.length = n * n
  lt : ∀ r ∈ R, r < p
  fits : len * p ≤ D
  piece : c0 + len ≤ n
  size : m = D * n
  spaceM : base + m < lim.space
  spaceR : res + n * n < lim.space
  spaceP : 2 * p < lim.space
  apart : Apart base m res (n * n)

namespace WritePre

variable {μ μ' : ℕ → ℤ} {base m res n D p c0 len : ℕ} {R : List ℕ}

/-- The number n of vertices fits in a word. -/
theorem n_le_word (pre : WritePre lim μ base m res n D p c0 len R) : (n : ℤ) ≤ lim.word := by
  have := pre.hw
  have := pre.spaceR
  nlinarith

/-- The length of the piece fits in a word. -/
theorem len_le_word (pre : WritePre lim μ base m res n D p c0 len R) : (len : ℤ) ≤ lim.word := by
  have := pre.n_le_word
  have := pre.piece
  omega

/-- The place of the weight between the vertex u and the c-th member c0 + c of the piece. -/
theorem index_lt (pre : WritePre lim μ base m res n D p c0 len R) {u c : ℕ} (hu : u < n)
    (hc : c < len) : u * n + c0 + c < n * n := by
  have := pre.piece
  nlinarith

/-- The residues can be read at any time. -/
theorem read (pre : WritePre lim μ base m res n D p c0 len R) (h : SameOutside μ μ' base m) {i : ℕ}
    (hi : i < n * n) : μ' (res + i) = (R.getD i 0 : ℕ) := by
  have hap := pre.apart
  have hil : i < R.length := pre.length ▸ hi
  rw [h _ (by omega), pre.seg _ (by simp_all), List.getElem_map,
    List.getD_eq_getElem _ 0 hil]

/-- The residues are below p. -/
theorem getD_lt (pre : WritePre lim μ base m res n D p c0 len R) {i : ℕ} (hi : i < n * n) :
    R.getD i 0 < p := by
  have hil : i < R.length := pre.length ▸ hi
  rw [List.getD_eq_getElem _ 0 hil]
  exact pre.lt _ (List.getElem_mem hil)

/-- The label s of the c-th member of the piece is one of the D middle vertices. -/
theorem middle_lt (pre : WritePre lim μ base m res n D p c0 len R) {c s : ℕ} (hc : c < len)
    (hs : s < p) : c * p + s < D :=
  (Nat.mul_add_lt_mul hc hs).trans_le pre.fits

end WritePre

/-! ## The two matrix layouts -/

namespace WriteMatrix

/-- Both writers use the same locals. The Y writer has no shift argument, so slot 7 starts at 0. -/
registers [Base, Residues, Verts, Middle, Prime, Start, Len, Shift, I, J, Label, Cells]

/-- X stores `(vertex, label)`; Y stores `(label, vertex)`. -/
@[simp] def axis {α : Type} : Bool → α → α → α
  | false, a, _ => a
  | true, _, b => b

def raw (right : Bool) (p rho r : ℕ) : ℕ := axis right (r + rho) (p - r)

def readResidue : Expr :=
  M (v Residues +' (v I *' v Verts +' v Start +' v J))

def rawExpr (right : Bool) : Expr :=
  axis right (readResidue +' v Shift) (v Prime -' readResidue)

def markExpr (right : Bool) : Expr :=
  let lab := v J *' v Prime +' v Label
  v Base +' axis right (v I *' v Middle +' lab) (lab *' v Verts +' v I)

def normalizeLabel : Stmt :=
  .ite (v Label <' v Prime) .skip (.set Label (v Label -' v Prime))

def cell (right : Bool) : Stmt :=
  .set Label (rawExpr right) ;; normalizeLabel ;; .store (markExpr right) (k 1)

def body (right : Bool) : Stmt :=
  .set Cells (v Verts *' v Middle) ;;
  pass I (v Cells) (v Base) (k 0) ;;
  .for I (v Verts) (.for J (v Len) (cell right))

abbrev locals (base res n D p c0 len rho m : ℕ) (i j t : ℤ) : List ℤ :=
  [base, res, n, D, p, c0, len, rho, i, j, t, m]

end WriteMatrix

open WriteMatrix

abbrev writeXBody : Stmt := body false
abbrev writeYBody : Stmt := body true

def tWrite (n D len : ℕ) : ℕ := 13 * (n * D) + n * (42 * len + 14) + 16

abbrev labX (n p c0 rho : ℕ) (R : List ℕ) (a c : ℕ) : ℕ := (R.getD (a * n + c0 + c) 0 + rho) % p
abbrev labY (n p c0 : ℕ) (R : List ℕ) (c b : ℕ) : ℕ := (p - R.getD (b * n + c0 + c) 0) % p

abbrev posX (n D p c0 rho : ℕ) (R : List ℕ) (a c : ℕ) : ℕ := a * D + (c * p + labX n p c0 rho R a c)
abbrev posY (n p c0 : ℕ) (R : List ℕ) (c b : ℕ) : ℕ := (c * p + labY n p c0 R c b) * n + b

/-- Entry i of yList, the matrix Y row by row, is 1 if one of the pairs (c, b) marks the cell i, and
0 if not. -/
theorem getElem_yList {n D p c0 len : ℕ} {RBC : List ℕ} (hp : 0 < p) {i : ℕ}
    (hi : i < (yList n D p c0 len RBC).length) :
    (yList n D p c0 len RBC)[i] = markVal (fun b c => posY n p c0 RBC c b) len n 0 i := by
  have hi' : i < D * n := by simpa [yList] using hi
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp_all
  rw [markVal_end
    (i / n / p < len ∧ i / n % p = (p - RBC.getD (i % n * n + c0 + i / n / p) 0) % p)]
  · simp [yList]
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨i % n, Nat.mod_lt _ hn, i / n / p, h1, ?_⟩
      rw [posY, labY, ← h2, Nat.mul_comm (i / n / p) p, Nat.div_add_mod, Nat.mul_comm (i / n) n,
        Nat.div_add_mod]
    · rintro ⟨b, hb, c, hc, rfl⟩
      have hl : labY n p c0 RBC c b < p := Nat.mod_lt _ hp
      rw [posY, Nat.mul_add_div_of_lt hb, Nat.mul_add_mod_of_lt hb, Nat.mul_add_div_of_lt hl,
        Nat.mul_add_mod_of_lt hl]
      trivial

/-- Entry i of xList, the matrix X row by row, is 1 if one of the pairs (a, c) marks the cell i, and
0 if not. -/
theorem getElem_xList {n D p c0 len rho : ℕ} {RAC : List ℕ} (hp : 0 < p) (hD : len * p ≤ D) {i : ℕ}
    (hi : i < (xList n D p c0 len rho RAC).length) :
    (xList n D p c0 len rho RAC)[i] = markVal (posX n D p c0 rho RAC) len n 0 i := by
  have hi' : i < n * D := by simpa [xList] using hi
  rw [markVal_end
    (i % D / p < len ∧ i % D % p = (RAC.getD (i / D * n + c0 + i % D / p) 0 + rho) % p)]
  · simp [xList]
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨i / D, Nat.div_lt_of_lt_mul' hi', i % D / p, h1, ?_⟩
      rw [posX, labX, ← h2, Nat.mul_comm (i % D / p) p, Nat.div_add_mod, Nat.mul_comm (i / D) D,
        Nat.div_add_mod]
    · rintro ⟨a, ha, c, hc, rfl⟩
      have hl : labX n p c0 rho RAC a c < p := Nat.mod_lt _ hp
      have hcol : c * p + labX n p c0 rho RAC a c < D := (Nat.mul_add_lt_mul hc hl).trans_le hD
      rw [posX, Nat.mul_add_div_of_lt hcol, Nat.mul_add_mod_of_lt hcol, Nat.mul_add_div_of_lt hl,
        Nat.mul_add_mod_of_lt hl]
      exact ⟨hc, rfl⟩

section writer

variable {μ μ' : ℕ → ℤ} {base res n D p c0 len rho : ℕ} {R : List ℕ}

private abbrev position (right : Bool) (n D p c0 rho : ℕ) (R : List ℕ) : ℕ → ℕ → ℕ :=
  axis right (posX n D p c0 rho R) (fun i j => posY n p c0 R j i)

private theorem position_lt (right : Bool)
    (pre : WritePre lim μ base (n * D) res n D p c0 len R)
    {i j : ℕ} (hi : i < n) (hj : j < len) : position right n D p c0 rho R i j < n * D := by
  have hp := pre.getD_lt (pre.index_lt hi hj)
  have hm := pre.middle_lt hj (Nat.mod_lt (raw right p rho (R.getD
    (i * n + c0 + j) 0)) (by omega : 0 < p))
  cases right
  · exact Nat.mul_add_lt_mul hi hm
  · rw [Nat.mul_comm n D]
    exact Nat.mul_add_lt_mul hm hi

private theorem write_spec (right : Bool)
    (pre : WritePre lim μ base (n * D) res n D p c0 len R)
    (hrho : right = false → rho < p) {xs : List ℤ} (hlen : xs.length = n * D)
    (get : ∀ i (hi : i < xs.length), xs[i] = markVal (position right n D p c0 rho R) len n 0 i) :
    Ends lim P d (body right) ⟨frame [base, res, n, D, p, c0, len, rho], μ⟩
      (tWrite n D len) fun σ' => Seg σ'.mem base xs ∧ SameOutside μ σ'.mem base (n * D) := by
  have hw := pre.hw
  have hs := pre.spaceM
  unfold body
  light_set (n * D : ℕ) using tWrite
  refine Ends.next _ (clear_spec hw hs (by decide) (by decide) rfl rfl
    (fun ν hzero hrest => ?_)) (by light_time [tWrite])
  let L := fun t : ℤ => frame (locals base res n D p c0 len rho (n * D) (n * D) 0 t)
  let pos := position right n D p c0 rho R
  refine Ends.forRect (x := Verts) (y := Len) (b := 34) L
    (fun i j _ ν' => Marked μ ν' base (n * D) pos len i j) 0 (.start hzero hrest)
    pre.n_le_word pre.len_le_word (fun _ => rfl) (fun _ => rfl) ?_
    (fun _ _ _ _ h => h.row) (fun _ _ _ h => ⟨h.seg hlen get, h.rest⟩)
    (hT := by light_time [tWrite])
  intro i j t ν' hi hj h
  simp only [L, rectLoc, update_frame_setLocal]
  let q := i * n + c0 + j
  let r := R.getD q 0
  let a := raw right p rho r
  let lab := a % p
  let idx := axis right (i * D + (j * p + lab)) ((j * p + lab) * n + i)
  have hq := pre.index_lt hi hj
  have hread := pre.read h.rest hq
  have hr : r < p := pre.getD_lt hq
  have ha : a < 2 * p := by cases right <;> simp_all [a, raw] <;> omega
  have hp : 0 < p := Nat.zero_lt_of_lt hr
  have hlab : lab < p := Nat.mod_lt _ hp
  have hm := pre.middle_lt hj hlab
  have heq : idx = position right n D p c0 rho R i j := by cases right <;> rfl
  have hpos : idx < n * D := heq ▸ position_lt right pre hi hj
  have hmul : 0 ≤ ((j : ℤ) * p + lab) * n := by positivity
  have hiD : 0 ≤ (i : ℤ) * D := by positivity
  have hjp : 0 ≤ (j : ℤ) * p := by positivity
  have hspace := pre.spaceM
  have hspaceP := pre.spaceP
  have hspaceR := pre.spaceR
  have hw := pre.hw
  have hnD : D ≤ n * D := Nat.le_mul_of_pos_left _ (by omega)
  have haddr : (↑res + ((i : ℤ) * n + c0 + j)).toNat = res + q := by
    simp only [q, ← Int.natCast_add, ← Int.natCast_mul, Int.toNat_natCast]
  unfold cell
  refine Ends.setToThen (a : ℤ) ?_ ?_ (by cases right <;> decide)
  · refine Ends.pieceThen (T₁ := 8) (R := fun σ => σ = ⟨frame (locals base res n D p c0 len rho
      (n * D) i j lab), ν'⟩) ?_ ?_ (by cases right <;> decide)
    · unfold normalizeLabel
      refine Ends.iteLast (fun h => ?_) (fun h => ?_)
      · have h' : a < p := by change (a : ℤ) < p at h; exact_mod_cast h
        exact Ends.skip (by simp [lab, Nat.mod_eq_of_lt h', locals])
      · have h' : p ≤ a := by change ¬ (a : ℤ) < p at h; omega
        have he : lab = a - p := by
          change a % p = a - p
          rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)]
        exact Ends.setTo (lab : ℤ) rfl (by light_side [he])
    · rintro _ rfl
      refine Ends.storeTo (base + idx) 1 ⟨lab, rfl, by simpa [pos, ← heq, idx, Nat.mul_comm] using h.step hj (position_lt right pre hi hj)⟩ ?_ (by cases right <;> decide)
      dsimp only [idx] at hpos ⊢
      generalize lab = label at hm hpos hmul ⊢
      cases right <;> simp only [axis] at hpos ⊢ <;> zify at hm hpos hspace <;>
        simp [abs_le, -abs_mul, markExpr] <;> zify <;> omega
  · cases right <;> simp [rawExpr, readResidue, q, r, a, raw] at hq hr ha hread ⊢ <;>
      light_side [haddr, hread, a, raw, r, q, Int.ofNat_sub hr.le]

/-- Write X in row-major order. -/
theorem writeX_spec (pre : WritePre lim μ base (n * D) res n D p c0 len R) (hrho : rho < p) :
    Ends lim P d writeXBody ⟨frame [base, res, n, D, p, c0, len, rho], μ⟩ (tWrite n D len)
      fun σ' => Seg σ'.mem base (xList n D p c0 len rho R) ∧ SameOutside μ σ'.mem base (n * D) :=
  write_spec false pre (fun _ => hrho) (by simp [xList])
    (fun _ hi => getElem_xList (by omega) pre.fits hi)

/-- Write Y in row-major order. Unlike X, its labels are negated residues. -/
theorem writeY_spec (pre : WritePre lim μ base (D * n) res n D p c0 len R) :
    Ends lim P d writeYBody ⟨frame [base, res, n, D, p, c0, len], μ⟩ (tWrite n D len)
      fun σ' => Seg σ'.mem base (yList n D p c0 len R) ∧ SameOutside μ σ'.mem base (D * n) := by
  rw [Nat.mul_comm D n] at pre ⊢
  rw [← frame_append_zeros _ 1]
  refine write_spec true (rho := 0) pre (by simp) (by simp [yList, Nat.mul_comm]) fun i hi => getElem_yList ?_ hi
  have hi' : i < D * n := by simpa [yList] using hi
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi'
  have hR : 0 < R.length := pre.length ▸ Nat.mul_pos hn hn
  exact Nat.zero_lt_of_lt (pre.lt _ (List.getElem_mem hR))

end writer
end Light.Sec3
