/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Auto
public import ThreeSumApsp.Lang.Lib.Pass
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
* `markPairs` runs the two loops, given what the body does for one pair (`MarkCtx`);
* `writeYCell_spec` and `writeXCell_spec` treat the bodies: read a residue, form the label, mark the
  cell;
* `getElem_yList` and `getElem_xList` identify the marks of all pairs with the matrices.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Marking cells: the pure side -/

section

/-- The cell i has been marked when the pairs (u', w'), w' < W, before (u, w) in lexicographic order
have been handled; the pair (u', w') marks the cell pos u' w'. -/
def CellMarked (pos : Light.SolverTime) W u w i :=
  ∃ u' w', (u' < u ∨ u' = u ∧ w' < w) ∧ w' < W ∧ pos u' w' = i

open Classical in
/-- The content of the cell i when the pairs before (u, w) have been handled: 1 if it has been
marked, else 0. -/
noncomputable def markVal (pos : Light.SolverTime) (W u w i : ℕ) : ℤ :=
  if CellMarked pos W u w i then 1 else 0

variable {pos : Light.SolverTime} {W u w i : ℕ}

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
  · grind [Light.Sec3.CellMarked]

theorem markVal_row : markVal pos W u W i = markVal pos W (u + 1) 0 i := by
  unfold markVal
  congr 1
  grind [Light.Sec3.CellMarked]

/-- At the end, a cell is marked iff it is the cell of one of the pairs. -/
theorem markVal_end {U} q [Decidable q] (h : q ↔ ∃ u' < U, ∃ w' < W, pos u' w' = i) :
    markVal pos W U 0 i = if q then 1 else 0 := by
  unfold markVal
  have : CellMarked pos W U 0 i ↔ q := by
    simp_all [Light.Sec3.CellMarked]
  simp_all

end

/-! ## Marking cells: the memory -/

/-- The m cells from base hold the marks of the pairs before (u, w), and no other cell has
changed. -/
structure Marked (μ μ' : Light.Memory) (base m : ℕ) (pos : Light.SolverTime) (W u w : ℕ) : Prop where
  cells : ∀ i < m, μ' (base + i) = markVal pos W u w i
  rest : SameOutside μ μ' base m

namespace Marked

variable {μ μ' : Light.Memory} {base m : ℕ} {pos : Light.SolverTime} {U W u w : ℕ}

/-- After the clearing no pair has been handled. -/
theorem start (hzero : ∀ i < m, μ' (base + i) = 0) (hrest : SameOutside μ μ' base m) :
    Marked μ μ' base m pos W 0 0 :=
  ⟨fun i hi => by ram_arith [markVal_zero], hrest⟩

/-- The pair (u, w) marks its cell. -/
theorem step (h : Marked μ μ' base m pos W u w) (hlt : w < W) (hpos : pos u w < m) :
    Marked μ (Function.update μ' (base + pos u w) 1) base m pos W u (w + 1) := by
  refine ⟨fun i hi => ?_, h.rest.update ⟨by omega, by omega⟩ _⟩
  rw [markVal_step hlt]
  split_ifs with e
  · rw [e, Function.update_self]
  · ram_arith

/-- The end of a row of pairs is the beginning of the next row. -/
theorem row (h : Marked μ μ' base m pos W u W) : Marked μ μ' base m pos W (u + 1) 0 :=
  ⟨fun i hi => by ram_arith [markVal_row], h.rest⟩

/-- When all pairs have been handled, the cells hold the list of all marks. -/
theorem seg {l} (h : Marked μ μ' base m pos W U 0) (hlen : l.length = m)
    (hget : ∀ i hi, l[i] = markVal pos W U 0 i) : Seg μ' base l :=
  fun i hi => by ram_safe

end Marked

/-! ## Marking cells: the two loops -/

/-- What the two loops `for u < U: for w < W: cell` need.  L u w t is the list of the locals: u and
w are the counters, in the locals cu and cw, and t is a temporary of the body.  The body takes at
most b steps and marks the cell of the pair (u, w). -/
structure MarkCtx (lim : Limits) (P : Program) (d : ℕ) (μ : Light.Memory) (base m U W b : ℕ)
    (pos : Light.SolverTime) (cu cw : ℕ) (hiU hiW : Expr) (cell : Stmt) (L : ℤ → ℤ → ℤ → List ℤ) :
    Prop where
  wordU : (U : ℤ) ≤ lim.word
  wordW : (W : ℤ) ≤ lim.word
  atU : ∀ u w t, frame (L u w t) cu = u
  atW : ∀ u w t, frame (L u w t) cw = w
  setU : ∀ u w t z, setLocal (L u w t) cu z = L z w t
  setW : ∀ u w t z, setLocal (L u w t) cw z = L u z t
  boundU : ∀ u w t μ', hiU.Gives lim ⟨frame (L u w t), μ'⟩ U
  boundW : ∀ u w t μ', hiW.Gives lim ⟨frame (L u w t), μ'⟩ W
  pos_lt : ∀ u w, u < U → w < W → pos u w < m
  cell_spec : ∀ (u w : ℕ) (t : ℤ) (μ' : Light.Memory), u < U → w < W → SameOutside μ μ' base m →
    Ends lim P d cell ⟨frame (L u w t), μ'⟩ b fun σ' =>
      ∃ t', σ' = ⟨frame (L u w t'), Function.update μ' (base + pos u w) 1⟩

section

variable {μ μ' : Light.Memory} {base m U W b : ℕ} {pos : Light.SolverTime} {cu cw : ℕ} {hiU hiW : Expr}
  {cell : Stmt} {L : ℤ → ℤ → ℤ → List ℤ}

variable (C : MarkCtx lim P d μ base m U W b pos cu cw hiU hiW cell L)

include C in
/-- The inner loop: the pairs (u, 0), …, (u, W - 1) mark their cells. -/
theorem markRow  {u} (hu : u < U)
     w₀ t₀ (h : Marked μ μ' base m pos W u 0) :
    Ends lim P d (.for cw hiW cell) ⟨frame (L u w₀ t₀), μ'⟩ (W * (hiW.cost + b + 7) + hiW.cost + 5)
      fun σ' => ∃ w t μ'', σ' = ⟨frame (L u w t), μ''⟩ ∧ Marked μ μ'' base m pos W (u + 1) 0 := by
  refine Ends.for
    (fun w σ => ∃ t μ'', σ = ⟨frame (L u w t), μ''⟩ ∧ Marked μ μ'' base m pos W u w) W b
    ?start ?round ?done ?bound C.wordW le_rfl
  case start => exact ⟨t₀, μ', by simp only [update_frame_setLocal, C.setW, Nat.cast_zero], h⟩
  case bound =>
    ram_arith
  case round =>
    rintro w _ hlt - ⟨t, μ'', rfl, hm⟩
    refine (C.cell_spec u w t μ'' hu hlt hm.rest).mono le_rfl ?_
    rintro _ ⟨t', rfl⟩
    exact ⟨C.atW _ _ _, t', _,
      by simp only [update_frame_setLocal, C.setW, Nat.cast_add, Nat.cast_one],
      hm.step hlt (C.pos_lt u w hu hlt)⟩
  case done =>
    rintro _ - ⟨t, μ'', rfl, hm⟩
    exact ⟨W, t, μ'', rfl, hm.row⟩

include C in
/-- **The two loops**: all pairs mark their cells. -/
theorem markPairs  u₀ w₀ t₀
    (h : Marked μ μ' base m pos W 0 0) :
    Ends lim P d (.for cu hiU (.for cw hiW cell)) ⟨frame (L u₀ w₀ t₀), μ'⟩
      (U * (hiU.cost + (W * (hiW.cost + b + 7) + hiW.cost + 5) + 7) + hiU.cost + 5)
      fun σ' => Marked μ σ'.mem base m pos W U 0 := by
  refine Ends.for
    (fun u σ => ∃ w t μ'', σ = ⟨frame (L u w t), μ''⟩ ∧ Marked μ μ'' base m pos W u 0) U _
    ?start ?round ?done ?bound C.wordU le_rfl
  case start => exact ⟨w₀, t₀, μ', by simp only [update_frame_setLocal, C.setU, Nat.cast_zero], h⟩
  case bound =>
    ram_arith
  case round =>
    rintro u _ hu - ⟨w, t, μ'', rfl, hm⟩
    refine (markRow C hu w t hm).mono le_rfl ?_
    rintro _ ⟨w', t', μ₃, rfl, hm'⟩
    exact ⟨C.atU _ _ _, w', t', μ₃,
      by simp only [update_frame_setLocal, C.setU, Nat.cast_add, Nat.cast_one], hm'⟩
  case done =>
    aesop

end

/-! ## Clearing the matrix -/

/-- The loop that clears a matrix: local 0 holds its address base, local t the number m of its
cells, and local c is the counter.  Afterwards the m cells hold 0, and no other cell has changed. -/
theorem clear_spec {μ} {l} {c t base m} {Q}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : base + m < lim.space) (hc : 0 ≠ c) (ht : t ≠ c)
    (hbase : frame l 0 = base) (hm : frame l t = m)
    (h : ∀ μ', (∀ i < m, μ' (base + i) = 0) → SameOutside μ μ' base m →
      Q ⟨frame (setLocal l c m), μ'⟩) :
    Ends lim P d (.for c (v t) (.store (v 0 +' v c) (k 0))) ⟨frame l, μ⟩ (13 * m + 6) Q := by
  refine Ends.pass (x := t) (y := 0) (dst := base) (n := m) (fun _ => 0)
    (fun j _ => ⟨?_, rfl⟩) ?_ hw (by omega) hm hbase ht hc
  · light_side
  · rw [update_frame_setLocal]
    exact h _ (fun i hi => wrote_done hi) (sameOutside_wrote le_rfl)

/-! ## What both routines assume -/

/-- The residues R of the n² weights, all below p, stand at res.  The matrix has m = D n cells at
base, apart from the residues.  The piece {c0, …, c0 + len - 1} lies within the n vertices, and its
len p labels within the D middle vertices. -/
structure WritePre (lim : Limits) (μ : Light.Memory) (base m res n D p c0 len : ℕ) (R : List ℕ) :
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

variable {μ μ' : Light.Memory} {base m res n D p c0 len : ℕ} {R : List ℕ}

variable (pre : WritePre lim μ base m res n D p c0 len R)

include pre in
/-- The number n of vertices fits in a word. -/
theorem n_le_word : (n : ℤ) ≤ lim.word := by
  ram_safe

include pre in
/-- The length of the piece fits in a word. -/
theorem len_le_word : (len : ℤ) ≤ lim.word := by
  ram_safe

include pre in
/-- The place of the weight between the vertex u and the c-th member c0 + c of the piece. -/
theorem index_lt {u c} (hu : u < n)
    (hc : c < len) : u * n + c0 + c < n * n := by
  ram_safe

include pre in
/-- The residues can be read at any time. -/
theorem read (h : SameOutside μ μ' base m) {i}
    (hi : i < n * n) : μ' (res + i) = R.getD i 0 := by
  have  := pre.apart
  have hil := pre.length ▸ hi
  rw [h _ (by omega), pre.seg _ (by simpa using hil), List.getElem_map,
    List.getD_eq_getElem _ 0 hil]

include pre in
/-- The residues are below p. -/
theorem getD_lt {i} (hi : i < n * n) :
    R.getD i 0 < p := by
  ram_arith

/-- The label s of the c-th member of the piece is one of the D middle vertices. -/
def middle_lt (pre : WritePre lim μ base m res n D p c0 len R) {c s} (hc : c < len)
    (hs : s < p) :=
  (Nat.mul_add_lt_mul hc hs).trans_le pre.fits

end WritePre

/-! ## The matrix Y -/


/-- The pair (c, b) marks its cell: r := rbc[b n + c0 + c]; if r ≠ 0 then r := p - r;
y[(c p + r) n + b] := 1. -/
def writeYCell  :=
  .set 9 (M (v 1 +' v 8 *' v 2 +' v 5 +' v 7)) ;;
  .ite (v 9 =' k 0) .skip (.set 9 (v 4 -' v 9)) ;;
  .store (v 0 +' (v 7 *' v 4 +' v 9) *' v 2 +' v 8) (k 1)

/-- writeY(y, rbc, n, D, p, c0, len). -/
def writeYBody  :=
  .set 10 (v 3 *' v 2) ;;
  .for 7 (v 10) (.store (v 0 +' v 7) (k 0)) ;;
  .for 7 (v 6) (.for 8 (v 2) writeYCell)

/-- The time of writeY. -/
def tWriteY n D len := 13 * (D * n) + len * (40 * n + 14) + 16

/-- The label of the row that the pair (c, b) marks. -/
def labY n p c0 (RBC : List ℕ) c b := (p - RBC.getD (b * n + c0 + c) 0) % p

/-- The cell that the pair (c, b) marks. -/
def posY n p c0 RBC c b := (c * p + labY n p c0 RBC c b) * n + b

/-- Entry i of yList, the matrix Y row by row, is 1 if one of the pairs (c, b) marks the cell i, and
0 if not. -/
theorem getElem_yList {n D p c0 len} {RBC} (hp : 0 < p) {i}
     hi :
    (yList n D p c0 len RBC)[i] = markVal (posY n p c0 RBC) n len 0 i := by
  have hi' := by simpa [yList] using hi

  rw [markVal_end
    (i / n / p < len ∧ i / n % p = (p - RBC.getD (i % n * n + c0 + i / n / p) 0) % p)]
  · simp [yList]
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨i / n / p, h1, i % n, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by simp [h] at hi'), ?_⟩
      rw [posY, labY, ← h2, Nat.mul_comm (i / n / p) p, Nat.div_add_mod, Nat.mul_comm (i / n) n,
        Nat.div_add_mod]
    · rintro ⟨c, hc, b, hb, rfl⟩
      have hl : labY n p c0 RBC c b < p := Nat.mod_lt _ hp
      rw [posY, Nat.mul_add_div_of_lt hb, Nat.mul_add_mod_of_lt hb, Nat.mul_add_div_of_lt hl,
        Nat.mul_add_mod_of_lt hl]
      exact ⟨hc, rfl⟩

section

variable {μ μ' : Light.Memory} {y rbc n D p c0 len : ℕ} {RBC : List ℕ}

variable (pre : WritePre lim μ y (D * n) rbc n D p c0 len RBC)

include pre in
/-- The cell of a pair lies in the matrix. -/
theorem posY_lt  {c b} (hc : c < len)
    (hb : b < n) : posY n p c0 RBC c b < D * n := by
  have  := pre.getD_lt (pre.index_lt hb hc)
  exact Nat.mul_add_lt_mul (pre.middle_lt hc (Nat.mod_lt _ (by omega))) hb

/-- The label, as the program computes it. -/
theorem labY_eq {c b} (hr : RBC.getD (b * n + c0 + c) 0 < p) : labY n p c0 RBC c b =
    if RBC.getD (b * n + c0 + c) 0 = 0 then 0 else p - RBC.getD (b * n + c0 + c) 0 := by
  unfold labY
  split_ifs with h
  · simp_all
  · exact Nat.mod_eq_of_lt (by omega)

include pre in
/-- **One pair of writeY.** -/
theorem writeYCell_spec  {c b } (t )
    (hc : c < len) (hb : b < n) (hrest : SameOutside μ μ' y (D * n)) :
    Ends lim P d writeYCell ⟨frame [y, rbc, n, D, p, c0, len, c, b, t, D * n], μ'⟩ 32
      fun σ' => ∃ t', σ' = ⟨frame [y, rbc, n, D, p, c0, len, c, b, t', D * n],
        Function.update μ' (y + posY n p c0 RBC c b) 1⟩ := by
  light_facts pre
  have hidx := pre.index_lt hb hc
  have hread := pre.read hrest hidx
  have hr := pre.getD_lt hidx
  have hlab := labY_eq hr
  have hpos : (c * p + labY n p c0 RBC c b) * n + b < D * n := posY_lt pre hc hb
  have  : c * p + labY n p c0 RBC c b < D := pre.middle_lt hc (Nat.mod_lt _ (by omega))
  have  : D ≤ D * n := Nat.le_mul_of_pos_right D (by omega)
  have  : ((c : ℤ) * p + labY n p c0 RBC c b) * n + b < D * n := mod_cast hpos
  have  : 0 ≤ ((c : ℤ) * p + labY n p c0 RBC c b) * n := by positivity

  generalize RBC.getD (b * n + c0 + c) 0 = r at hread hr hlab
  -- y[(c p + r) n + b] := 1, once r is the label
  have mark : ∀ s , labY n p c0 RBC c b = s →
      Ends lim P d (.store (v 0 +' (v 7 *' v 4 +' v 9) *' v 2 +' v 8) (k 1))
        ⟨frame [y, rbc, n, D, p, c0, len, c, b, s, D * n], μ'⟩ 13 fun σ' =>
          ∃ t', σ' = ⟨frame [y, rbc, n, D, p, c0, len, c, b, t', D * n],
            Function.update μ' (y + posY n p c0 RBC c b) 1⟩ := by
    rintro _ rfl
    exact Ends.storeTo (y + posY n p c0 RBC c b) 1 ⟨_, rfl⟩
      (by light_side [posY])
  -- r := rbc[b n + c0 + c]
  light_set (r : ℕ) using (by omega : ((rbc : ℤ) + b * n + c0 + c).toNat = rbc + (b * n + c0 + c)), hread
  -- if r ≠ 0 then r := p - r
  refine Ends.next 8 (Ends.iteLast (fun h0 => Ends.skip (mark _ ?_)) fun h0 =>
    Ends.setTo (p - r : ℕ) (mark _ ?_))
  · simp_all
  · simp_all

include pre in
/-- The two loops of writeY are loops that mark cells. -/
theorem writeY_markCtx  :
    MarkCtx lim P d μ y (D * n) len n 32 (posY n p c0 RBC) 7 8 (v 6) (v 2) writeYCell
      fun c b t => [y, rbc, n, D, p, c0, len, c, b, t, D * n] where
  wordU := pre.len_le_word
  wordW := pre.n_le_word
  atU _ _ _ := rfl
  atW _ _ _ := rfl
  setU _ _ _ _ := rfl
  setW _ _ _ _ := rfl
  boundU _ _ _ _ := by simp
  boundW _ _ _ _ := by simp
  pos_lt _ _ hc hb := posY_lt pre hc hb
  cell_spec _ _ t _ hc hb hrest := writeYCell_spec pre t hc hb hrest

include pre in
/-- **writeY** writes the matrix Y and changes nothing else. -/
theorem writeY_spec  :
    Ends lim P d writeYBody ⟨frame [y, rbc, n, D, p, c0, len], μ⟩ (tWriteY n D len) fun σ' =>
      Seg σ'.mem y (yList n D p c0 len RBC) ∧ SameOutside μ σ'.mem y (D * n) := by
  light_facts pre
  unfold tWriteY
  -- sz := D n
  light_set (D * n : ℕ)
  -- for c < sz: y[c] := 0
  refine Ends.next _
    (clear_spec pre.hw pre.spaceM (by decide) (by decide) rfl rfl fun μ' hzero hrest => ?_)
  -- for c < len: for b < n: the pair (c, b) marks its cell
  refine (markPairs (writeY_markCtx pre) _ _ _ (.start hzero hrest)).mono ?_ fun σ' hm =>
    ⟨hm.seg (by simp [yList]) fun i hi => getElem_yList ?_ hi, hm.rest⟩
  · light_time
  · have hi' := by simpa [yList] using hi
    have  : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi'

    have := pre.lt _ (List.getElem_mem (by simp_all : 0 < RBC.length))
    omega

end

/-! ## The matrix X -/


/-- The pair (a, c) marks its cell: t := rac[a n + c0 + c] + rho; if p ≤ t then t := t - p;
x[a D + c p + t] := 1. -/
def writeXCell  :=
  .set 10 (M (v 1 +' v 8 *' v 2 +' v 5 +' v 9) +' v 7) ;;
  .ite (v 10 <' v 4) .skip (.set 10 (v 10 -' v 4)) ;;
  .store (v 0 +' v 8 *' v 3 +' v 9 *' v 4 +' v 10) (k 1)

/-- writeX(x, rac, n, D, p, c0, len, rho). -/
def writeXBody  :=
  .set 11 (v 2 *' v 3) ;;
  .for 8 (v 11) (.store (v 0 +' v 8) (k 0)) ;;
  .for 8 (v 2) (.for 9 (v 6) writeXCell)

/-- The time of writeX. -/
def tWriteX n D len := 13 * (n * D) + n * (42 * len + 14) + 16

/-- The label of the column that the pair (a, c) marks. -/
def labX n p c0 rho (RAC : List ℕ) a c := (RAC.getD (a * n + c0 + c) 0 + rho) % p

/-- The cell that the pair (a, c) marks. -/
def posX n D p c0 rho RAC a c :=
  a * D + (c * p + labX n p c0 rho RAC a c)

/-- Entry i of xList, the matrix X row by row, is 1 if one of the pairs (a, c) marks the cell i, and
0 if not. -/
theorem getElem_xList {n D p c0 len rho} {RAC} (hp : 0 < p) (hD : len * p ≤ D) {i}
     hi :
    (xList n D p c0 len rho RAC)[i] = markVal (posX n D p c0 rho RAC) len n 0 i := by

  rw [markVal_end
    (i % D / p < len ∧ i % D % p = (RAC.getD (i / D * n + c0 + i % D / p) 0 + rho) % p)]
  · simp [xList]
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨i / D, Nat.div_lt_of_lt_mul' (by simpa [xList] using hi), i % D / p, h1, ?_⟩
      rw [posX, labX, ← h2, Nat.mul_comm (i % D / p) p, Nat.div_add_mod, Nat.mul_comm (i / D) D,
        Nat.div_add_mod]
    · rintro ⟨a, ha, c, hc, rfl⟩
      have hl : labX n p c0 rho RAC a c < p := Nat.mod_lt _ hp
      have hcol := (Nat.mul_add_lt_mul hc hl).trans_le hD
      rw [posX, Nat.mul_add_div_of_lt hcol, Nat.mul_add_mod_of_lt hcol, Nat.mul_add_div_of_lt hl,
        Nat.mul_add_mod_of_lt hl]
      exact ⟨hc, rfl⟩

section

variable {μ μ' : Light.Memory} {x rac n D p c0 len rho : ℕ} {RAC : List ℕ}

variable (pre : WritePre lim μ x (n * D) rac n D p c0 len RAC)

include pre in
/-- The cell of a pair lies in the matrix. -/
theorem posX_lt  {a c} (ha : a < n)
    (hc : c < len) : posX n D p c0 rho RAC a c < n * D := by
  have  := pre.getD_lt (pre.index_lt ha hc)
  exact Nat.mul_add_lt_mul ha (pre.middle_lt hc (Nat.mod_lt _ (by omega)))

/-- The label, as the program computes it. -/
theorem labX_eq {a c} (hr : RAC.getD (a * n + c0 + c) 0 < p) (hrho : rho < p) :
    labX n p c0 rho RAC a c = if RAC.getD (a * n + c0 + c) 0 + rho < p
      then RAC.getD (a * n + c0 + c) 0 + rho else RAC.getD (a * n + c0 + c) 0 + rho - p := by
  unfold labX
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

include pre in
/-- **One pair of writeX.** -/
theorem writeXCell_spec  (hrho : rho < p)
    {a c } (t ) (ha : a < n) (hc : c < len) (hrest : SameOutside μ μ' x (n * D)) :
    Ends lim P d writeXCell ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, t, n * D], μ'⟩ 34
      fun σ' => ∃ t', σ' = ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, t', n * D],
        Function.update μ' (x + posX n D p c0 rho RAC a c) 1⟩ := by
  light_facts pre
  have hidx := pre.index_lt ha hc
  have hread := pre.read hrest hidx
  have hr := pre.getD_lt hidx
  have hlab := labX_eq hr hrho
  have  : a * D + (c * p + labX n p c0 rho RAC a c) < n * D := posX_lt pre ha hc

  generalize RAC.getD (a * n + c0 + c) 0 = r at hread hr hlab
  -- x[a D + c p + t] := 1, once t is the label
  have mark : ∀ s , labX n p c0 rho RAC a c = s →
      Ends lim P d (.store (v 0 +' v 8 *' v 3 +' v 9 *' v 4 +' v 10) (k 1))
        ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, s, n * D], μ'⟩ 13 fun σ' =>
          ∃ t', σ' = ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, t', n * D],
            Function.update μ' (x + posX n D p c0 rho RAC a c) 1⟩ := by
    rintro _ rfl
    exact Ends.storeTo (x + posX n D p c0 rho RAC a c) 1 ⟨_, rfl⟩ (by light_side [posX])
  -- t := rac[a n + c0 + c] + rho
  light_set (r + rho : ℕ) using (by omega : ((rac : ℤ) + a * n + c0 + c).toNat = rac + (a * n + c0 + c)), hread
  -- if p ≤ t then t := t - p
  refine Ends.next 8 (Ends.iteLast (fun h0 => Ends.skip (mark _ ?_)) fun h0 => ?_)
  · ram_safe
  · light_block []

include pre in
/-- The two loops of writeX are loops that mark cells. -/
theorem writeX_markCtx  (hrho : rho < p) :
    MarkCtx lim P d μ x (n * D) n len 34 (posX n D p c0 rho RAC) 8 9 (v 2) (v 6) writeXCell
      fun a c t => [x, rac, n, D, p, c0, len, rho, a, c, t, n * D] where
  wordU := pre.n_le_word
  wordW := pre.len_le_word
  atU _ _ _ := rfl
  atW _ _ _ := rfl
  setU _ _ _ _ := rfl
  setW _ _ _ _ := rfl
  boundU _ _ _ _ := by simp
  boundW _ _ _ _ := by simp
  pos_lt _ _ ha hc := posX_lt pre ha hc
  cell_spec _ _ t _ ha hc hrest := writeXCell_spec pre hrho t ha hc hrest

include pre in
/-- **writeX** writes the matrix X and changes nothing else. -/
theorem writeX_spec  (hrho : rho < p) :
    Ends lim P d writeXBody ⟨frame [x, rac, n, D, p, c0, len, rho], μ⟩ (tWriteX n D len) fun σ' =>
      Seg σ'.mem x (xList n D p c0 len rho RAC) ∧ SameOutside μ σ'.mem x (n * D) := by
  light_facts pre
  unfold tWriteX
  -- sz := n D
  light_set (n * D : ℕ)
  -- for a < sz: x[a] := 0
  refine Ends.next _
    (clear_spec pre.hw pre.spaceM (by decide) (by decide) rfl rfl fun μ' hzero hrest => ?_)
  -- for a < n: for c < len: the pair (a, c) marks its cell
  refine (markPairs (writeX_markCtx pre hrho) _ _ _ (.start hzero hrest)).mono ?_ fun σ' hm =>
    ⟨hm.seg (by simp [xList]) fun i hi => getElem_xList (by omega) pre.fits hi, hm.rest⟩
  light_time

end

end Light.Sec3
