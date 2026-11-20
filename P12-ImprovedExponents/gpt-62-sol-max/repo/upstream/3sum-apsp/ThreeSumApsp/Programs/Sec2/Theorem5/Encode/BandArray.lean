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
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.BandArrayFacts

/-!
# The input array of a band (Section 2.3.4)

Section 2.3.3: "a[u] := X_Q[u], b[v] := Y_Q[v] for all the left strings u and the right strings v
whose inner set Q has exactly m elements, and a[u] := 0, b[v] := 0 at every other string"; in
Section 2.3.4, X_Q and Y_Q are the row block and the column block of the block product with subset
Q.  bandArray writes this input array for a row band of X or a column band of Y.  The array is
laid out by the codes of the left (right) strings and filled in the order of the tuples: the
procedure clears the array, and then, for every block product (g, h) of a tile, every row r of the
block and every column k, it computes the code of the string digit by digit and copies one entry of
the matrix.

Two rectangular traversals fill the block products and the entries of each tile, respectively.
`coverRect` tracks the cells already filled. `bandArray_entry` handles either orientation.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

/-! ## The program -/

namespace Band

/-- The local variables of bandArray.  The arguments: `Levels` = L, `Size` = m, `Rows` = N, `Cols` =
D, `NumBlocks` = K0, `Width` = N0, `Cells` = S7, `BandNo` = β, `Side` = side; `Source` is the
address of the matrix, `StepRow` and `StepCol` the steps from row to row and from column to column;
`MaskTable`, `Digits3`, `Digits4` and `Dest` are the addresses of the table of subsets, of the two
tables of digits and of the array.  Then, by the depth of the loop that uses them: `PosG` = g (also
the counter of the clearing loop); `PosH` = h, `BlockIdx` the number of the block, `MaskRow` the
address of the mask of the subset; `Offset` = r, `Row` the number of the row of the matrix; `Col` =
k, `CodeAcc` the code, `Outer` and `Inner` the addresses of the next outer and of the next inner
digit, `CurLevel` the level. -/
registers [Levels, Size, Rows, Cols, NumBlocks, Width, Cells, BandNo, Side, Source, StepRow,
  StepCol, MaskTable, Digits3, Digits4, Dest, PosG, PosH, BlockIdx, MaskRow, Offset, Row, Col,
  CodeAcc, Outer, Inner, CurLevel]

end Band

open Band

/-- One level: Horner's rule in base 7, with the next outer digit, or 3 plus the next inner
digit. -/
def bandLevel : Stmt :=
  .ite (M (v MaskRow +' v CurLevel) =' k 0)
    (.set CodeAcc (v CodeAcc *' k 7 +' M (v Outer)) ;; .set Outer (v Outer +' k 1))
    (.set CodeAcc (v CodeAcc *' k 7 +' k 3 +' M (v Inner)) ;; .set Inner (v Inner +' k 1))

/-- The loop over the levels. -/
def bandCodeLoop : Stmt := .for CurLevel (v Levels) bandLevel

/-- One entry: the code of the string, and the entry copied. -/
def bandCell : Stmt :=
  .set CodeAcc (k 0) ;;
  .set Outer (v Digits3 +' v Row *' (v Levels -' v Size)) ;;
  .set Inner (v Digits4 +' v Col *' v Size) ;;
  bandCodeLoop ;;
  .store (v Dest +' v CodeAcc) (M (v Source +' v Row *' v StepRow +' v Col *' v StepCol))

/-- A cell contributes only when its row belongs to the matrix. -/
def bandRowCell : Stmt :=
  .set Row (v BlockIdx *' v Width +' v Offset) ;;
  .ite (v Row <' v Rows) bandCell .skip

def bandTile : Stmt := .for Offset (v Width) (.for Col (v Cols) bandRowCell)

def bandBlock : Stmt :=
  .ite (v Side =' k 0) (.set BlockIdx (v BandNo *' v NumBlocks +' v PosG))
    (.set BlockIdx (v BandNo *' v NumBlocks +' v PosH)) ;;
  .set MaskRow (v MaskTable +' (v PosG *' v NumBlocks +' v PosH) *' v Levels) ;; bandTile

def bandGLoop : Stmt := .for PosG (v NumBlocks) (.for PosH (v NumBlocks) bandBlock)

/-- The clearing loop. -/
def bandZeroLoop : Stmt := pass PosG (v Cells) (v Dest) (k 0)

/-- bandArray(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr). -/
def bandArrayBody : Stmt := bandZeroLoop ;; bandGLoop

/-- The constant of the running time. -/
def cBandArray : ℕ := 120

/-! ## The local variables as a list -/

/-- The local variables of the loop over h. -/
structure BlockTmp where
  /-- h. -/
  h : ℤ
  /-- The number of the block. -/
  blk : ℤ
  /-- The address of the mask of the subset. -/
  mrow : ℤ

/-- The local variables of the loop over the rows of a block. -/
structure RowTmp where
  /-- r. -/
  r : ℤ
  /-- The number of the row of the matrix. -/
  row : ℤ

/-- The local variables of the loop over the columns. -/
structure CellTmp where
  /-- k. -/
  k : ℤ
  /-- The code. -/
  code : ℤ
  /-- The address of the next outer digit. -/
  outer : ℤ
  /-- The address of the next inner digit. -/
  inner : ℤ
  /-- The level. -/
  lev : ℤ

/-- The local variables of the three inner loops together. -/
structure InnerTmp where
  /-- Those of the loop over `h`. -/
  block : BlockTmp
  /-- Those of the loop over the rows of a block. -/
  row : RowTmp
  /-- Those of the loop over the columns. -/
  cell : CellTmp

/-- The list of the local variables. -/
abbrev Band.locals (A : BandArgs) (g : ℤ) (H : BlockTmp) (R : RowTmp) (c : CellTmp) : List ℤ :=
  [A.p.L, A.p.m, A.p.N, A.p.D, A.p.K0, A.p.N0, A.p.S7, A.β, A.side, A.aA, A.sI, A.sK, A.mask,
    A.dig3, A.dig4, A.arr, g, H.h, H.blk, H.mrow, R.r, R.row, c.k, c.code, c.outer, c.inner, c.lev]

/-- The local variables of the loop over `h` for the block product `(g, h)`. -/
abbrev Band.blockTmp (A : BandArgs) (g h : ℕ) : BlockTmp :=
  ⟨h, (A.blockNo g h : ℕ), (A.maskRow g h : ℕ)⟩

/-- The local variables of the loop over the rows for the row `r` of the block product `(g, h)`. -/
abbrev Band.rowTmp (A : BandArgs) (g h r : ℕ) : RowTmp := ⟨r, (A.rowNo g h r : ℕ)⟩

variable {lim : Limits} {P : Program} {d : ℕ} {A : BandArgs} {μ₀ μ : ℕ → ℤ} {T : List ℤ}

/-! ## The loop over the levels -/

/-- What the loop over the levels reads: the mask bs at mrow, the outer digits o at d3 and the inner
digits i at d4. -/
structure CodeCtx (lim : Limits) (μ : ℕ → ℤ) (L mrow d3 d4 : ℕ) (bs : List Bool) (o i : List ℕ) :
    Prop where
  std : Std lim
  length : bs.length = L
  outer : bs.count false = o.length
  inner : bs.count true = i.length
  outer_lt : ∀ x ∈ o, x < 3
  inner_lt : ∀ x ∈ i, x < 4
  segB : SegB μ mrow bs
  segO : SegN μ d3 o
  segI : SegN μ d4 i
  spaceB : mrow + L ≤ lim.space
  spaceO : d3 + o.length ≤ lim.space
  spaceI : d4 + i.length ≤ lim.space
  space7 : 7 ^ L ≤ lim.space

/-- The local variables of the loop over the columns after l levels. -/
abbrev Band.codeTmp (k : ℤ) (bs : List Bool) (o i : List ℕ) (d3 d4 l : ℕ) (lev : ℤ) : CellTmp :=
  ⟨k, (codeUpTo bs o i l : ℕ), (d3 + (bs.take l).count false : ℕ),
    (d4 + (bs.take l).count true : ℕ), lev⟩

section levels
variable {mrow d3 d4 : ℕ} {bs : List Bool} {o i : List ℕ} {g h blk k : ℤ} {R : RowTmp}

/-- **One level** leads from the state after `l` levels to the state after `l + 1` levels.  No cell
changes. -/
theorem bandLevel_spec (ctx : CodeCtx lim μ A.p.L mrow d3 d4 bs o i) {l : ℕ} (hl : l < A.p.L) :
    Ends lim P d bandLevel ⟨frame (locals A g ⟨h, blk, mrow⟩ R (codeTmp k bs o i d3 d4 l l)), μ⟩
      bandLevel.blockCost fun σ' =>
        σ' = ⟨frame (locals A g ⟨h, blk, mrow⟩ R (codeTmp k bs o i d3 d4 (l + 1) l)), μ⟩ := by
  light_facts ctx.std
  have hplaces := And.intro ctx.spaceB <| And.intro ctx.spaceO <| And.intro ctx.spaceI <|
    And.intro ctx.space7 <| And.intro ctx.outer ctx.inner
  have hlen : l < bs.length := ctx.length ▸ hl
  have hbit := ctx.segB.get hlen
  have hcode := codeUpTo_succ (o := o) (i := i) hlen
  have hlt := codeUpTo_lt ctx.outer_lt ctx.inner_lt (show l + 1 ≤ bs.length from hlen)
  have hpow : 7 ^ (l + 1) ≤ 7 ^ A.p.L := Nat.pow_le_pow_right (by omega) hl
  have hfalse := List.count_take_succ_getD bs false hlen false
  have htrue := List.count_take_succ_getD bs true hlen false
  unfold bandLevel
  cases hb : bs.getD l false
  · -- A level outside the set: the next outer digit.
    have hroom := List.count_take_lt hlen false hb
    have hcell := ctx.segO.read (ctx.outer ▸ hroom)
    rw [hb] at hbit hcode hfalse htrue
    simp only [Bool.false_eq_true, if_false, if_true] at hbit hcode hfalse htrue
    rw [hcode] at hlt
    generalize o.getD ((bs.take l).count false) 0 = digit at hcell hcode hlt
    refine Ends.iteLast (fun _ => ?_) (fun hc => absurd (by simp [hbit]) hc)
    -- CodeAcc := CodeAcc * 7 + mem[Outer]; Outer := Outer + 1
    light_set (codeUpTo bs o i (l + 1) : ℕ) using hcell, hcode
    light_block using false, hfalse, locals, setLocal, htrue
  · -- A level of the set: 3 plus the next inner digit.
    have hroom := List.count_take_lt hlen false hb
    have hcell := ctx.segI.read (ctx.inner ▸ hroom)
    rw [hb] at hbit hcode hfalse htrue
    simp only [if_true, reduceCtorEq, if_false,
      List.getD_map_of_lt (3 + ·) (ctx.inner ▸ hroom) 0 0] at hbit hcode hfalse htrue
    rw [hcode] at hlt
    generalize i.getD ((bs.take l).count true) 0 = digit at hcell hcode hlt
    refine Ends.iteLast (fun hc => absurd hc (by simp [hbit])) (fun _ => ?_)
    -- CodeAcc := CodeAcc * 7 + 3 + mem[Inner]; Inner := Inner + 1
    light_set (codeUpTo bs o i (l + 1) : ℕ) using hcell, hcode
    light_block using true, htrue, locals, setLocal, hfalse

/-- **The loop over the levels** leaves the code of the string in the local `CodeAcc` and changes no
cell. -/
theorem bandCodeLoop_spec (ctx : CodeCtx lim μ A.p.L mrow d3 d4 bs o i) {lev₀ : ℤ} {T' : ℕ}
    {Q : State → Prop}
    (done : ∀ c : CellTmp, c.k = k → c.code = (codeUpTo bs o i A.p.L : ℕ) →
      Q ⟨frame (locals A g ⟨h, blk, mrow⟩ R c), μ⟩)
    (hT : 28 * A.p.L + 6 ≤ T') :
    Ends lim P d bandCodeLoop ⟨frame (locals A g ⟨h, blk, mrow⟩ R ⟨k, 0, d3, d4, lev₀⟩), μ⟩ T'
      Q := by
  light_facts ctx ctx.std
  -- for CurLevel < L
  refine Ends.for (fun l σ =>
      σ = ⟨frame (locals A g ⟨h, blk, mrow⟩ R (codeTmp k bs o i d3 d4 l l)), μ⟩) A.p.L
    bandLevel.blockCost ?start ?round ?done ?bound (by omega) (by simp [bandLevel]; omega)
  case start => simp [update_frame_setLocal, locals, codeUpTo, ThreeSumApsp.ofDigitList]
  case done => simp_all
  case bound => simp_all
  case round =>
    rintro l _ hl - rfl
    refine (bandLevel_spec ctx hl).mono le_rfl ?_
    rintro _ rfl
    light_block using locals

end levels

/-! ## The surroundings -/

/-- Everything that the loops assume: the limits, the places of the tables and of the matrix in the
memory μ₀ at the start, and what is known about the list T that has to be produced. -/
structure BandCtx (lim : Limits) (A : BandArgs) (μ₀ : ℕ → ℤ) (T : List ℤ) : Prop where
  std : Std lim
  hmL : A.p.m ≤ A.p.L
  space : A.arr + A.p.S7 ≤ lim.space
  aA_le : A.aA + A.p.N * A.p.D ≤ A.arr
  tabs : BandTables A.p μ₀ A.mask A.dig3 A.dig4 A.arr
  β_lt : A.β < A.p.nB
  idx : ∀ row < A.p.N, ∀ k < A.p.D, row * A.sI + k * A.sK < A.p.N * A.p.D
  T_len : T.length = A.p.S7
  entry : ∀ g < A.p.K0, ∀ h < A.p.K0, ∀ r < A.p.N0, ∀ k < A.p.D, T.getD (A.code g h r k) 0
    = if A.rowNo g h r < A.p.N
      then μ₀ (A.aA + (A.rowNo g h r * A.sI + k * A.sK)) else 0
  zero : ∀ c : ℕ, (∀ g < A.p.K0, ∀ h < A.p.K0, ∀ r < A.p.N0, ∀ k < A.p.D,
    c ≠ A.code g h r k) → T.getD c 0 = 0

/-- The cell of the tuple (g, h, r, k) is right. -/
def Covered (A : BandArgs) (T : List ℤ) (μ : ℕ → ℤ) (g h r k : ℕ) : Prop :=
  μ (A.arr + A.code g h r k) = T.getD (A.code g h r k) 0

/-- A cell that is right stays right. -/
theorem Covered.keep {μ' : ℕ → ℤ} {g h r k : ℕ} (hc : Covered A T μ g h r k)
    (hext : OverwrittenWith T A.arr A.p.S7 μ μ') : Covered A T μ' g h r k :=
  hext.keep (BandArgs.code_lt ..) hc

local macro "band_facts " c:term:max a:term:max : tactic => `(tactic|
  (light_facts $c ($c).std ($c).tabs
   obtain ⟨_, _, _, _⟩ := ($a).p.sizes_le_S7
   have : ($a).p.N ≤ ($a).p.N * ($a).p.D := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))))

namespace BandCtx

/-- What the loop over the levels reads for the tuple (g, h, r, k), in a memory in which only cells
of the array have changed. -/
private theorem codeCtx (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    {g h r k : ℕ} (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0)
    (hrow : A.rowNo g h r < A.p.N) (hk : k < A.p.D) :
    CodeCtx lim μ A.p.L (A.maskRow g h)
      (A.dig3 + A.rowNo g h r * A.p.Lo) (A.dig4 + k * A.p.m)
      (Spec.unrank A.p.L A.p.m (g * A.p.K0 + h)) (ThreeSumApsp.digitList 3 (A.p.L - A.p.m) r)
      (ThreeSumApsp.digitList 4 A.p.m k) := by
  band_facts C A
  obtain ⟨hKK, hchoose⟩ := subsetIndex_lt A.p hg hh
  have hmask := Nat.mul_add_le_mul hKK (le_refl A.p.L)
  have hdig3 := Nat.mul_add_le_mul hrow (le_refl A.p.Lo)
  have hdig4 := Nat.mul_add_le_mul hk (le_refl A.p.m)
  have hLo : A.p.Lo = A.p.L - A.p.m := rfl
  have hS7 : A.p.S7 = 7 ^ A.p.L := rfl
  have hmaskRow : A.maskRow g h = A.mask + (g * A.p.K0 + h) * A.p.L := rfl
  -- The table of digits in base 3 is indexed by the row of the matrix and holds the digits of the
  -- offset of the row in its block, which is r.
  have hdigits := C.tabs.hdig3 _ hrow
  rw [BandArgs.rowNo_mod g h hr] at hdigits
  exact
    { std := C.std
      length := Spec.length_unrank ..
      outer := by rw [Spec.count_false_unrank hchoose, ThreeSumApsp.length_digitList]
      inner := by rw [Spec.count_unrank hchoose, ThreeSumApsp.length_digitList]
      outer_lt := fun _ => ThreeSumApsp.lt_of_mem_digitList (by omega)
      inner_lt := fun _ => ThreeSumApsp.lt_of_mem_digitList (by omega)
      segB := (C.tabs.hmask _ hKK).keep
      segO := hdigits.keep
      segI := (C.tabs.hdig4 k hk).keep
      spaceB := by omega
      spaceO := by rw [ThreeSumApsp.length_digitList]; omega
      spaceI := by rw [ThreeSumApsp.length_digitList]; omega
      space7 := by omega }

end BandCtx

/-- Both rectangular traversals preserve old entries and establish a fact for each pair. -/
private theorem coverRect {X : Type} {n m r c x y b U : ℕ} {body : Stmt} {Q : State → Prop}
    (L : X → ℕ → ℤ) (z : X) (fact : ℕ → ℕ → (ℕ → ℤ) → Prop)
    (keep : ∀ i j ν ν', fact i j ν → OverwrittenWith T A.arr A.p.S7 ν ν' → fact i j ν')
    (step : ∀ i j t ν, i < n → j < m → OverwrittenWith T A.arr A.p.S7 μ ν →
      Ends lim P d body ⟨rectLoc (L t) r c i j, ν⟩ b fun σ =>
        ∃ t', σ.loc = rectLoc (L t') r c i j ∧ OverwrittenWith T A.arr A.p.S7 ν σ.mem ∧
          fact i j σ.mem)
    (done : ∀ t j ν, OverwrittenWith T A.arr A.p.S7 μ ν → (∀ i < n, ∀ j' < m, fact i j' ν) →
      Q ⟨rectLoc (L t) r c n j, ν⟩)
    (hn : (n : ℤ) ≤ lim.word) (hm : (m : ℤ) ≤ lim.word)
    (hx : ∀ t, L t x = n) (hy : ∀ t, L t y = m)
    (hrc : r ≠ c := by decide) (hxr : x ≠ r := by decide) (hxc : x ≠ c := by decide)
    (hyr : y ≠ r := by decide) (hyc : y ≠ c := by decide)
    (hT : n * (m * (b + 8) + 14) + 6 ≤ U := by light_time) :
    Ends lim P d (.for r (v x) (.for c (v y) body)) ⟨L z, μ⟩ U Q := by
  refine Ends.forRect L (fun i j _ ν => OverwrittenWith T A.arr A.p.S7 μ ν ∧
    ∀ i' < n, ∀ j' < m, (i' < i ∨ i' = i ∧ j' < j) → fact i' j' ν) z
    ⟨.refl, by simp⟩ hn hm hx hy ?_ ?_ ?_ hrc hxr hxc hyr hyc hT
  · rintro i j t ν hi hj ⟨he, hf⟩
    refine (step i j t ν hi hj he).mono le_rfl ?_
    rintro σ ⟨t', hl, he', hf'⟩
    refine ⟨t', hl, he.trans he', fun i' hi' j' hj' hp => ?_⟩
    grind
  all_goals (grind)

/-- The time of one entry. -/
def tBandCell (p : Par) : ℕ := 28 * p.L + 36

section cell
variable {g h r k : ℕ}

/-- **One entry**: the code of the string is computed, and the entry of the matrix is copied to its
cell. -/
theorem bandCell_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0)
    (hrow : A.rowNo g h r < A.p.N) (hk : k < A.p.D) (c : CellTmp) :
    Ends lim P d bandCell
      ⟨frame (locals A g (blockTmp A g h) (rowTmp A g h r) { c with k := k }), μ⟩ (tBandCell A.p)
      fun σ' => ∃ c' : CellTmp, σ' =
        ⟨frame (locals A g (blockTmp A g h) (rowTmp A g h r) { c' with k := k }),
          Function.update μ (A.arr + A.code g h r k) (T.getD (A.code g h r k) 0)⟩ := by
  band_facts C A
  have hdig3 := Nat.mul_add_le_mul hrow (le_refl A.p.Lo)
  have hdig4 := Nat.mul_add_le_mul hk (le_refl A.p.m)
  have hidx := C.idx _ hrow k hk
  have hcode := A.code_lt g h r k
  have hval : μ (A.aA + (A.rowNo g h r * A.sI + k * A.sK))
      = T.getD (A.code g h r k) 0 := by
    rw [C.entry g hg h hh r hr k hk, if_pos hrow]
    exact same _ (Or.inl (by omega))
  have ctx := C.codeCtx same hg hh hr hrow hk
  unfold rowTmp
  generalize A.rowNo g h r = row at *
  have houter : (row : ℤ) * ((A.p.L : ℤ) - A.p.m) = ((row * A.p.Lo : ℕ) : ℤ) := by
    rw [Nat.cast_mul, show A.p.Lo = A.p.L - A.p.m from rfl, Nat.cast_sub C.hmL]
  have haddr : ((A.aA : ℤ) + row * A.sI + k * A.sK).toNat = A.aA + (row * A.sI + k * A.sK) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, Int.toNat_natCast,
      Nat.add_assoc]
  unfold bandCell tBandCell
  -- CodeAcc := 0; Outer := dig3 + Row (L - m); Inner := dig4 + Col m
  light_steps using houter
  -- The code.
  refine Ends.next _ (bandCodeLoop_spec ctx ?_ le_rfl)
  rintro ⟨_, _, outer, inner, lev⟩ rfl rfl
  rw [show codeUpTo _ _ _ A.p.L = A.code g h r k from codeUpTo_unrank ..]
  -- mem[arr + CodeAcc] := mem[aA + Row sI + Col sK]
  light_step using haddr, hval
  exact ⟨⟨k, (A.code g h r k : ℕ), outer, inner, lev⟩, rfl⟩

end cell

/-- Cells of this tile are right whenever the row lies in the matrix. -/
def CoveredCell (A : BandArgs) (T : List ℤ) (μ : ℕ → ℤ) (g h r k : ℕ) : Prop :=
  A.rowNo g h r < A.p.N → Covered A T μ g h r k

def tBandRows (p : Par) : ℕ := p.N0 * (p.D * (tBandCell p + 10 + 8) + 14) + 6

/-- The time of one block product. -/
def tBandBlock (p : Par) : ℕ := tBandRows p + 20

private def tBandG (p : Par) : ℕ := p.K0 * (p.K0 * (tBandBlock p + 8) + 14) + 6

/-! ## The whole procedure -/

/-- The time of the whole procedure is within the bound that its callers assume. -/
private theorem bandArray_time (p : Par) :
    p.S7 * 13 + 6 + tBandG p ≤ cBandArray * bandArrayShape p := by
  have hD : 1 ≤ p.D := Nat.pow_pos (by omega)
  have hN0 : 1 ≤ p.N0 := N0_pos _ _
  have hK0 : p.K0 ≤ p.K0 * p.K0 := Nat.le_mul_self _
  have hKK : p.K0 * p.K0 ≤ p.K0 * p.K0 * p.N0 := Nat.le_mul_of_pos_right _ hN0
  have hrows : p.K0 * p.K0 * p.N0 ≤ p.K0 * p.K0 * p.N0 * p.D := Nat.le_mul_of_pos_right _ hD
  have htime : tBandG p = 28 * (p.K0 * p.K0 * p.N0 * p.D * p.L) + 54 * (p.K0 * p.K0 * p.N0 * p.D)
      + 14 * (p.K0 * p.K0 * p.N0) + 34 * (p.K0 * p.K0) + 14 * p.K0 + 6 := by
    unfold tBandG tBandBlock tBandRows tBandCell
    ring
  have hshape : cBandArray * bandArrayShape p = 120 * p.S7
      + 120 * (p.K0 * p.K0 * p.N0 * p.D * p.L) + 120 * (p.K0 * p.K0 * p.N0 * p.D) + 120 * p.L
      + 120 := by
    unfold cBandArray bandArrayShape Par.KK
    ring
  omega

/-- The arguments of bandArray as a list. -/
abbrev Band.args (A : BandArgs) : List ℤ :=
  [A.p.L, A.p.m, A.p.N, A.p.D, A.p.K0, A.p.N0, A.p.S7, A.β, A.side, A.aA, A.sI, A.sK, A.mask,
    A.dig3, A.dig4, A.arr]

/-- **bandArray** writes the list T to the array and changes nothing else. -/
theorem bandArray_spec (C : BandCtx lim A μ₀ T) :
    Ends lim P d bandArrayBody ⟨frame (args A), μ₀⟩ (cBandArray * bandArrayShape A.p) fun σ' =>
      Seg σ'.mem A.arr T ∧ SameOutside μ₀ σ'.mem A.arr A.p.S7 := by
  band_facts C A
  have htime := bandArray_time A.p
  have hcleared : SameOutside μ₀ (wrote μ₀ A.arr (fun _ => 0) A.p.S7) A.arr A.p.S7 :=
    sameOutside_wrote le_rfl
  -- The array is cleared.
  refine Ends.next _ (Ends.pass (x := Cells) (y := Dest) (dst := A.arr) (n := A.p.S7) (fun _ => 0)
    (fun j _ => by light_side) ?_ C.std.space_le C.space rfl rfl (hT := le_rfl)) (by simp; omega)
  -- The loops over the tuples (g, h, r, k); the ten local variables of the inner loops start at 0.
  rw [update_frame_setLocal, ← frame_append_zeros _ 10]
  let z₀ : InnerTmp := ⟨⟨0, 0, 0⟩, ⟨0, 0⟩, ⟨0, 0, 0, 0, 0⟩⟩
  have hD : A.p.D ≤ A.p.S7 := (Nat.pow_le_pow_right (by decide : 0 < 4) C.hmL).trans
    (Nat.pow_le_pow_left (by decide : 4 ≤ 7) _)
  refine coverRect (x := NumBlocks) (y := NumBlocks) (b := tBandBlock A.p)
    (fun t : InnerTmp => frame (locals A A.p.S7 t.block t.row t.cell)) z₀
    (fun g h ν => ∀ r < A.p.N0, ∀ k < A.p.D, CoveredCell A T ν g h r k)
    (fun _ _ _ _ hf he r hr k hk hy => (hf r hr k hk hy).keep he)
    ?_ ?_ (by omega) (by omega) (fun _ => rfl) (fun _ => rfl)
    (hT := by
      change tBandG A.p ≤ cBandArray * bandArrayShape A.p - (A.p.S7 * 13 + 6)
      omega)
  · intro g h t ν hg hh he
    simp only [rectLoc, update_frame_setLocal]
    have hsmall := BandArgs.rowNo_lt C.β_lt hg hh (N0_pos A.p.L A.p.m)
    obtain ⟨hKK, hchoose⟩ := subsetIndex_lt A.p hg hh
    have hmask := Nat.mul_add_le_mul hKK (le_refl A.p.L)
    have hprod : (((g * A.p.K0 + h) * A.p.L : ℕ) : ℤ) = ((g : ℤ) * A.p.K0 + h) * A.p.L := by
      push_cast
      rfl
    unfold bandBlock tBandBlock
    refine Ends.pieceThen (T₁ := 10) (R := (· =
      ⟨frame (locals A g ⟨h, (A.blockNo g h : ℕ), t.block.mrow⟩ t.row t.cell), ν⟩)) ?_ ?_
    · refine Ends.iteIffLast (A.side = 0) (fun hs => ?_) (fun hs => ?_) <;>
        refine Ends.setLast (by simp [update_frame_setLocal, locals, BandArgs.blockNo, hs]) ?_
      all_goals simp [abs_le, BandArgs.blockNo, hs] at hsmall ⊢; omega
    · rintro _ rfl
      light_set (A.maskRow g h : ℕ) using BandArgs.maskRow, hprod
      have hs := hcleared.trans he.1
      refine coverRect (x := Width) (y := Cols) (b := tBandCell A.p + 10)
        (fun z : RowTmp × CellTmp => frame (locals A g (blockTmp A g h) z.1 z.2)) (t.row, t.cell)
        (fun r k ν => CoveredCell A T ν g h r k) (fun _ _ _ _ hf he hy => (hf hy).keep he)
        ?_ ?_ (by omega) (by omega) (fun _ => rfl) (fun _ => rfl) (hT := by simp [tBandRows])
      · intro i j z ν' hi hj he'
        simp only [rectLoc, update_frame_setLocal]
        have hsmall := BandArgs.rowNo_lt C.β_lt hg hh hi
        have hrowNo : A.rowNo g h i = A.blockNo g h * A.p.N0 + i := rfl
        unfold bandRowCell
        light_step using hrowNo
        refine Ends.iteIffLast (A.rowNo g h i < A.p.N) (fun hy => ?_) (fun hn => ?_)
        · refine (bandCell_spec C (hs.trans he'.1) hg hh hi hy hj z.2).mono (by light_time) ?_
          rintro _ ⟨c', rfl⟩
          exact ⟨(rowTmp A g h i, c'), rfl, .write (A.code_lt ..), fun _ => Function.update_self ..⟩
        · light_skip
          exact ⟨(rowTmp A g h i, z.2), rfl, .refl, fun hrow => absurd hrow hn⟩
      · intro z k ν' hnew hf
        exact ⟨⟨blockTmp A g h, {z.1 with r := A.p.N0}, {z.2 with k := k}⟩,
          by simp only [rectLoc, update_frame_setLocal]; rfl, hnew, hf⟩
  · intro z j μ' hext hcov
    refine ⟨fun c hc => ?_, hcleared.trans hext.1⟩
    have hc7 : c < A.p.S7 := C.T_len ▸ hc
    rw [← List.getD_eq_getElem T 0 hc]
    -- A cell whose entry is 0 is right, whether it has been overwritten or not.
    have hzero : T.getD c 0 = 0 → μ' (A.arr + c) = T.getD c 0 := fun h0 =>
      (hext.2 c hc7).elim (fun h => by rw [h, wrote_done hc7, h0]) id
    by_cases hx : ∃ g < A.p.K0, ∃ h < A.p.K0, ∃ r < A.p.N0, ∃ k < A.p.D, c = A.code g h r k
    · obtain ⟨g, hg, h, hh, r, hr, k, hk, rfl⟩ := hx
      by_cases hrow : A.rowNo g h r < A.p.N
      · exact hcov g hg h hh r hr k hk hrow
      · exact hzero (by rw [C.entry g hg h hh r hr k hk, if_neg hrow])
    · exact hzero (C.zero c fun g hg h hh r hr k hk hce => hx ⟨g, hg, h, hh, r, hr, k, hk, hce⟩)

/-! ## What the callers assume -/

private abbrev BandArgs.ofSide (s : BandSide) (p : Par) (β aA mask dig3 dig4 arr : ℕ) : BandArgs :=
  ⟨p, β, s.tag, aA, s.strideI p, s.strideK p, mask, dig3, dig4, arr⟩

private def BandSide.indices (s : BandSide) {p : Par} (i : Fin p.N) (k : Fin p.D) :
    Fin (s.rows p) × Fin (s.cols p) := match s with
  | .left => (i, k)
  | .right => (k, i)

private theorem BandSide.offset (s : BandSide) {p : Par} (i : Fin p.N) (k : Fin p.D) :
    i.val * s.strideI p + k.val * s.strideK p =
      (s.indices i k).1.val * s.cols p + (s.indices i k).2.val := by
  cases s <;> simp [BandSide.indices, Nat.add_comm]

private theorem BandSide.at_code (s : BandSide) {p : Par} (hmL : p.m ≤ p.L) (X : s.Mat p)
    (β aA mask dig3 dig4 arr : ℕ) (g h : Fin p.K0) (r : Fin p.N0) (k : Fin p.D) :
    let A := BandArgs.ofSide s p β aA mask dig3 dig4 arr
    (Spec.arrStr s.alphabet (s.array hmL X β)).getD (A.code g h r k) 0 =
      if hi : A.rowNo g h r < p.N then
        let ij := s.indices ⟨A.rowNo g h r, hi⟩ k
        X ij.1 ij.2
      else 0 := by
  cases s
  · exact Spec.bandArrayL_at hmL X β g h r k
  · exact Spec.bandArrayR_at hmL X β g h r k

/-- The specification of bandArray is independent of which input orientation is used. -/
theorem bandArray_entry (std : Std lim) (hP : P[pBandArray]? = some bandArrayBody) :
    BandArraySpec lim P cBandArray := by
  intro s p hmL β aA mask dig3 dig4 arr μ X hsp hX hXle htab hβ d _
  let A := BandArgs.ofSide s p β aA mask dig3 dig4 arr
  have hsize : s.rows p * s.cols p = p.N * p.D := by cases s <;> simp [Nat.mul_comm]
  refine ⟨bandArrayBody, hP, bandArray_spec (A := A)
    { std := std, hmL := hmL, space := hsp, aA_le := hsize ▸ hXle, tabs := htab, β_lt := hβ
      T_len := Spec.length_arrStr _ _, idx := ?_, entry := ?_, zero := ?_ }⟩
  · intro i hi k hk
    let ij := s.indices ⟨i, hi⟩ ⟨k, hk⟩
    rw [show i * A.sI + k * A.sK = _ from s.offset ⟨i, hi⟩ ⟨k, hk⟩, ← hsize]
    exact Nat.mul_add_lt_mul ij.1.isLt ij.2.isLt
  · intro g hg h hh r hr k hk
    have he := s.at_code hmL X β aA mask dig3 dig4 arr ⟨g, hg⟩ ⟨h, hh⟩ ⟨r, hr⟩ ⟨k, hk⟩
    refine he.trans ?_
    by_cases hi : A.rowNo g h r < p.N
    · rw [dif_pos hi, if_pos hi]
      rw [show A.rowNo g h r * A.sI + k * A.sK = _ from s.offset ⟨_, hi⟩ ⟨k, hk⟩, ← Nat.add_assoc]
      exact (hX _ _).symm
    · rw [dif_neg hi, if_neg hi]
  · intro c hc
    have hz (g h : Fin p.K0) (r : Fin p.N0) (k : Fin p.D) := hc g g.2 h h.2 r r.2 k k.2
    cases s
    · exact Spec.bandArrayL_eq_zero hmL X β c hz
    · exact Spec.bandArrayR_eq_zero hmL X β c hz

end Light.Sec2
