module

public import ThreeSumApsp.Util.Index
public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Spec.Sec2.Theorem5.Layout
public import Mathlib.Algebra.Order.Ring.Int
public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Lang.Lib.Sqrt
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.BandArray
public import ImprovedExponents.PrunedProgram.Shared.Stage
public import ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.BruteForce
public import Mathlib.Data.Nat.Log
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts
public import ThreeSumApsp.Programs.Sec4.Theorem30.Directory
public import ThreeSumApsp.Spec.Sec4.Theorem30.PartialSums
public import ThreeSumApsp.Lang.Tactics
public import Mathlib.Data.Bool.Count
public import ThreeSumApsp.Lang.Lib.Pass
public import ImprovedExponents.PrunedProgram.Tiles.AllTiles
public import ImprovedExponents.PrunedProgram.Tiles.FillList
public import ImprovedExponents.PrunedProgram.Query.QuerySum
public import ThreeSumApsp.Programs.Sec4.Theorem30.NineNext
public import ImprovedExponents.PrunedProgram.Tiles.Tile
public import ThreeSumApsp.Lang.RowMajor
public import ThreeSumApsp.Programs.Sec4.Theorem30.WordSize

@[expose] public section

section



/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Quotients and remainders by counters

The word RAM has no division.  A program that runs through the rows `I = 0, 1, …, N - 1` of a matrix
can still know, for each row, its band, its block within the band and its offset within the block
(Section 2.3.4), that is `I / (K₀ N₀)`, `I / N₀ % K₀` and `I % N₀`: it keeps three counters and
steps them (`stepCtr`, `ctrAt_succ`).
-/


namespace ThreeSumApsp.Spec

/-- The band of a row, its block within the band, and its offset within the block. -/
structure Ctr where
  /-- The band of the row. -/
  band : ℕ
  /-- The block of the row within its band. -/
  block : ℕ
  /-- The offset of the row within its block. -/
  off : ℕ

/-- The band, block and offset of row `I`, for bands of `k₀` blocks of `n₀` rows. -/
def ctrAt (k₀ n₀ I : ℕ) : Ctr := ⟨I / (k₀ * n₀), I / n₀ % k₀, I % n₀⟩

/-- From the band, block and offset of a row to those of the next row: comparisons and additions of
1 only. -/
def stepCtr (k₀ n₀ : ℕ) (s : Ctr) : Ctr :=
  if s.off + 1 < n₀ then { s with off := s.off + 1 }
  else if s.block + 1 < k₀ then { s with block := s.block + 1, off := 0 }
  else ⟨s.band + 1, 0, 0⟩

/-- Stepping the counters of row `I` gives the counters of row `I + 1`. -/
theorem ctrAt_succ {k₀ n₀ : ℕ} (hk : 0 < k₀) (hn : 0 < n₀) (I : ℕ) :
    ctrAt k₀ n₀ (I + 1) = stepCtr k₀ n₀ (ctrAt k₀ n₀ I) := by
  have : I % n₀ < n₀ := Nat.mod_lt I hn
  have : I / n₀ % k₀ < k₀ := Nat.mod_lt _ hk
  simp only [ctrAt, stepCtr, Nat.mul_comm k₀ n₀, ← Nat.div_div_eq_div_mul]
  split_ifs with hoff hlt
  · -- The next row of the same block.
    obtain ⟨hdiv, hmod⟩ := Nat.succ_div_mod_of_lt hoff
    rw [hdiv, hmod]
  · -- The first row of the next block of the same band.
    obtain ⟨hdiv, hmod⟩ := Nat.succ_div_mod_of_eq (show I % n₀ + 1 = n₀ by omega)
    obtain ⟨hband, hblock⟩ := Nat.succ_div_mod_of_lt hlt
    rw [hdiv, hmod, hband, hblock]
  · -- The first row of the first block of the next band.
    obtain ⟨hdiv, hmod⟩ := Nat.succ_div_mod_of_eq (show I % n₀ + 1 = n₀ by omega)
    obtain ⟨hband, hblock⟩ := Nat.succ_div_mod_of_eq (show I / n₀ % k₀ + 1 = k₀ by omega)
    rw [hdiv, hmod, hband, hblock]

end ThreeSumApsp.Spec

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Band and block of every row, by counting (Section 2.3.4)

Section 2.3.4 cuts the N rows of X into bands of K₀ blocks of N₀ rows.  counters(N, K0, N0, dst)
writes, for every row I < N, its band I / (K0 N0) to the cell dst + I and its block I / N0 % K0 to
the cell dst + N + I.  There is no division: three counters (band, block, offset) are stepped from
each row to the next, as `Spec.stepCtr` says, and `Spec.ctrAt_succ` says that they are the
quotients and remainders.

A round writes two cells (`Counted.step`) and steps the counters (`countersRound_spec`);
`counters_spec` runs through the rows, and `counters_entry` is the specification that the callers of
the procedure assume.
-/


namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Counters

/-- The local variables of counters: Total = N, Blocks = K0, Width = N0, Dest = dst (the arguments);
Row is the current row, and Band, Block, Offset are its band, its block and its offset. -/
abbrev Total : ℕ := 0
@[inherit_doc Total] abbrev Blocks : ℕ := 1
@[inherit_doc Total] abbrev Width : ℕ := 2
@[inherit_doc Total] abbrev Dest : ℕ := 3
@[inherit_doc Total] abbrev Row : ℕ := 4
@[inherit_doc Total] abbrev Band : ℕ := 5
@[inherit_doc Total] abbrev Block : ℕ := 6
@[inherit_doc Total] abbrev Offset : ℕ := 7

end Counters

open Counters in
/-- One round: the band and the block of the current row are written, and the counters move on to
the next row. -/
def countersRound : Stmt :=
  .store (v Dest +' v Row) (v Band) ;;
  .store (v Dest +' v Total +' v Row) (v Block) ;;
  .set Row (v Row +' k 1) ;;
  .set Offset (v Offset +' k 1) ;;
  .ite (v Offset <' v Width) .skip (
    .set Offset (k 0) ;;
    .set Block (v Block +' k 1) ;;
    .ite (v Block <' v Blocks) .skip (
      .set Block (k 0) ;;
      .set Band (v Band +' k 1)))

open Counters in
/-- counters(N, K0, N0, dst).  The row and the three counters are not set at the beginning: local
variables that are not arguments start at 0. -/
def countersBody : Stmt := .while (v Row <' v Total) countersRound

namespace Counters

variable {μ μ' : ℕ → ℤ} {N K0 N0 dst i : ℕ}

/-- The memory before round i: band and block of the rows below i are written, and no cell outside
the 2 N cells from dst has changed. -/
def Counted (μ : ℕ → ℤ) (N K0 N0 dst i : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ I < i, μ' (dst + I) = (I / (K0 * N0) : ℕ) ∧ μ' (dst + N + I) = (I / N0 % K0 : ℕ)) ∧
    SameOutside μ μ' dst (2 * N)

/-- The two cells that round i writes. -/
theorem Counted.step (h : Counted μ N K0 N0 dst i μ') (hi : i < N) :
    Counted μ N K0 N0 dst (i + 1) (Function.update (Function.update μ' (dst + i)
      ((Spec.ctrAt K0 N0 i).band : ℕ)) (dst + N + i) ((Spec.ctrAt K0 N0 i).block : ℕ)) := by
  refine ⟨fun I hI => ?_, (h.2.update ⟨by omega, by omega⟩ _).update ⟨by omega, by omega⟩ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hI with hI | rfl
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact h.1 I hI
  · rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self]
    exact ⟨rfl, rfl⟩

/-- The state before round i: the counters are those of row i. -/
def Inv (μ : ℕ → ℤ) (N K0 N0 dst i : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame [N, K0, N0, dst, i, (Spec.ctrAt K0 N0 i).band,
    (Spec.ctrAt K0 N0 i).block, (Spec.ctrAt K0 N0 i).off], μ'⟩ ∧ Counted μ N K0 N0 dst i μ'

end Counters

open Counters

variable {μ : ℕ → ℤ} {N K0 N0 dst : ℕ}

/-- **One round** writes the band and the block of row `i` and steps the counters to those of row
`i + 1`. -/
theorem countersRound_spec (std : Std lim) (hsp : dst + 2 * N ≤ lim.space) (hK : 0 < K0)
    (hN0 : 0 < N0) (hw : ((K0 + N0 : ℕ) : ℤ) ≤ lim.word) {i : ℕ} (hi : i < N) {σ : State}
    (h : Inv μ N K0 N0 dst i σ) :
    Ends lim P d countersRound σ countersRound.blockCost (Inv μ N K0 N0 dst (i + 1)) := by
  obtain ⟨μ', rfl, hI⟩ := h
  light_facts std
  push_cast at hw
  have hnext := Spec.ctrAt_succ hK hN0 i
  have hstep := hI.step hi
  have : (Spec.ctrAt K0 N0 i).band ≤ i := Nat.div_le_self _ _
  have : (Spec.ctrAt K0 N0 i).block < K0 := Nat.mod_lt _ hK
  have : (Spec.ctrAt K0 N0 i).off < N0 := Nat.mod_lt _ hN0
  generalize Spec.ctrAt K0 N0 i = c at *
  unfold countersRound
  rw [Spec.stepCtr] at hnext
  -- mem[dst + Row] := Band; mem[dst + N + Row] := Block; Row := Row + 1; Offset := Offset + 1
  light_store (dst + i) c.band
  light_store (dst + N + i) c.block
  light_set (i + 1 : ℕ)
  light_set (c.off + 1 : ℕ)
  -- if Offset < N0
  refine Ends.iteLast (fun hc => Ends.skip ⟨_, ?_, hstep⟩) fun hc => ?_
  · -- The next row of the same block.
    rw [hnext, if_pos (by simp at hc; omega)]
    rfl
  -- Offset := 0; Block := Block + 1; if Block < K0
  light_set 0
  light_set (c.block + 1 : ℕ)
  refine Ends.iteLast (fun hc' => Ends.skip ⟨_, ?_, hstep⟩) fun hc' => ?_
  · -- The first row of the next block of the same band.
    rw [hnext, if_neg (by simp at hc; omega), if_pos (by simp at hc'; omega)]
    rfl
  · -- The first row of the first block of the next band: Block := 0; Band := Band + 1
    refine Ends.setToThen 0 (Ends.setTo ((c.band + 1 : ℕ) : ℤ) ⟨_, ?_, hstep⟩)
    rw [hnext, if_neg (by simp at hc; omega), if_neg (by simp at hc'; omega)]
    rfl

/-- **counters** writes the band and the block of every row and changes nothing else. -/
theorem counters_spec (std : Std lim) (hsp : dst + 2 * N ≤ lim.space) (hK : 0 < K0) (hN0 : 0 < N0)
    (hw : ((K0 + N0 : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d countersBody ⟨frame [N, K0, N0, dst], μ⟩ (44 * (N + 1)) fun σ' =>
      (∀ I < N, σ'.mem (dst + I) = (I / (K0 * N0) : ℕ) ∧
        σ'.mem (dst + N + I) = (I / N0 % K0 : ℕ)) ∧ SameOutside μ σ'.mem dst (2 * N) := by
  have := std.space_le
  -- while Row < N; a round takes at most 40 steps
  refine Ends.whileConst (Inv μ N K0 N0 dst) N countersRound.blockCost ?start ?round ?done
    (by simp [countersRound]; omega)
  case start =>
    refine ⟨μ, ?_, fun I hI => absurd hI (by omega), .refl⟩
    -- The row and the three counters start at 0.
    rw [← frame_append_zeros _ 4]
    simp [Spec.ctrAt]
  case round =>
    intro i σ hi h
    have hround := countersRound_spec (P := P) (d := d) std hsp hK hN0 hw hi h
    obtain ⟨μ', rfl, -⟩ := h
    exact ⟨by light_side, by light_side, hround⟩
  case done =>
    rintro _ ⟨μ', rfl, hcells, same⟩
    exact ⟨by light_side, by light_side, hcells, same⟩

/-- **The specification that the callers of counters assume.** -/
theorem counters_entry (std : Std lim) (hP : P[pCounters]? = some countersBody) {c : ℕ}
    (hc : 44 ≤ c) : CountersSpec lim P c :=
  fun _ _ _ _ _ hsp hK hN0 hw _ _ => .mono_const (.of_body hP (counters_spec std hsp hK hN0 hw)) hc

end Light.Sec2

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# A binomial coefficient, by Pascal's triangle

Section 2.3.4 needs the number K = (L choose m) of subsets of size m.  binom(L, m, pas) returns this
binomial coefficient.  The cells pas, …, pas + L hold a row of Pascal's triangle.  Row 0 is 1
followed by zeros (`binomFirst_spec`), and the next row is formed in place, from right to left, so
that the two entries that are added are still those of the old row.  `binomPlace_spec` treats one
entry, by Pascal's rule, `binomInner_spec` one row, and `binom_spec` runs through the rows;
`binom_entry` is the specification that the callers of the procedure assume.
-/


namespace Light.Sec2

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Binom

/-- The local variables of binom: Levels = L, Size = m, Addr = pas (the arguments); Row is the
number of the row, and Place the place in it. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Size : ℕ := 1
@[inherit_doc Levels] abbrev Addr : ℕ := 2
@[inherit_doc Levels] abbrev Row : ℕ := 3
@[inherit_doc Levels] abbrev Place : ℕ := 4

end Binom

open Binom

/-- One entry of the next row: the entry above it plus the entry to the left of that. -/
def binomPlace : Stmt :=
  .store (v Addr +' v Place) (M (v Addr +' v Place) +' M (v Addr +' v Place -' k 1)) ;;
  .set Place (v Place -' k 1)

/-- The loop that turns row i of the triangle into row i + 1, from right to left. -/
def binomInner : Stmt := .while (k 0 <' v Place) binomPlace

/-- One round of the loop over the rows. -/
def binomRow : Stmt := .set Place (v Levels) ;; binomInner ;; .set Row (v Row +' k 1)

/-- Row 0 of the triangle: 1 followed by L zeros. -/
def binomFirst : Stmt :=
  .store (v Addr) (k 1) ;;
  .set Place (k 1) ;;
  .while (v Place <' v Levels +' k 1) (
    .store (v Addr +' v Place) (k 0) ;;
    .set Place (v Place +' k 1))

/-- binom(L, m, pas).  The number of the row is not set at the beginning: local variables that are
not arguments start at 0.  The result of a procedure is what it leaves in local variable 0. -/
def binomBody : Stmt :=
  binomFirst ;;
  .while (v Row <' v Levels) binomRow ;;
  .set Levels (M (v Addr +' v Size))

namespace Binom

/-! ## One row from the row before it -/

/-- The memory while row i is turned into row i + 1: the entries to the right of place p are those
of row i + 1, the others still those of row i; no cell outside the L + 2 cells that the procedure
may use has changed. -/
def Mixed (μ : ℕ → ℤ) (L pas i p : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ j ≤ L, μ' (pas + j) = if p < j then (((i + 1).choose j : ℕ) : ℤ) else (i.choose j : ℕ)) ∧
    SameOutside μ μ' pas (L + 2)

/-- One more entry has been replaced. -/
theorem Mixed.step {μ μ' : ℕ → ℤ} {L pas i p : ℕ} (h : Mixed μ L pas i (p + 1) μ')
    (hp : p + 1 ≤ L) :
    Mixed μ L pas i p (Function.update μ' (pas + (p + 1)) ((i + 1).choose (p + 1) : ℕ)) := by
  refine ⟨fun j hj => ?_, h.2.update ⟨by omega, by omega⟩ _⟩
  by_cases hjp : j = p + 1
  · rw [hjp, Function.update_self, if_pos (by omega)]
  · rw [Function.update_of_ne (by omega), h.1 j hj]
    exact if_congr (by omega) rfl rfl

variable {μ : ℕ → ℤ} {L m pas i : ℕ} {T : ℕ} {Q : State → Prop}

/-- The state after r entries have been replaced: the place is L - r. -/
def Inv (μ : ℕ → ℤ) (L m pas i r : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame [L, m, pas, i, (L - r : ℕ)], μ'⟩ ∧ Mixed μ L pas i (L - r) μ'

/-- **One entry**, by Pascal's rule. -/
theorem binomPlace_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space) (hi : i < L)
    (hw : ((2 ^ L : ℕ) : ℤ) ≤ lim.word) {r : ℕ} (hr : r < L) {σ : State}
    (h : Inv μ L m pas i r σ) :
    Ends lim P d binomPlace σ binomPlace.blockCost (Inv μ L m pas i (r + 1)) := by
  obtain ⟨μ', rfl, hI⟩ := h
  light_facts std
  obtain ⟨p, hp⟩ : ∃ p, L - r = p + 1 := ⟨L - r - 1, by omega⟩
  unfold Inv
  rw [hp] at hI ⊢
  rw [show L - (r + 1) = p by omega]
  -- The two entries that are added are still those of row i, and their sum fits in a word.
  have habove : μ' (pas + (p + 1)) = (i.choose (p + 1) : ℕ) := by
    rw [hI.1 (p + 1) (by omega), if_neg (by omega)]
  have hleft : μ' (pas + p) = (i.choose p : ℕ) := by rw [hI.1 p (by omega), if_neg (by omega)]
  have hsum : (i + 1).choose (p + 1) = i.choose p + i.choose (p + 1) := Nat.choose_succ_succ' i p
  have : (i + 1).choose (p + 1) ≤ 2 ^ L :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) hi)
  have haddr : ((pas : ℤ) + ((p : ℤ) + 1) - 1).toNat = pas + p := by omega
  have haddr' : ((pas : ℤ) + ((p : ℤ) + 1)).toNat = pas + (p + 1) := by omega
  unfold binomPlace
  -- mem[pas + Place] := mem[pas + Place] + mem[pas + Place - 1]; Place := Place - 1
  light_store (pas + (p + 1)) ((i + 1).choose (p + 1) : ℕ) using habove, hleft, haddr, haddr', hsum
  light_set p
  exact ⟨_, rfl, hI.step (by omega)⟩

/-- **One row**: the loop over the places turns row i of the triangle into row i + 1. -/
theorem binomInner_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space) (hi : i < L)
    (hw : ((2 ^ L : ℕ) : ℤ) ≤ lim.word) (hrow : ∀ j ≤ L, μ (pas + j) = (i.choose j : ℕ))
    (done : ∀ μ' : ℕ → ℤ, (∀ j ≤ L, μ' (pas + j) = ((i + 1).choose j : ℕ)) →
      SameOutside μ μ' pas (L + 2) → Q ⟨frame [L, m, pas, i, 0], μ'⟩)
    (hT : 23 * L + 4 ≤ T) :
    Ends lim P d binomInner ⟨frame [L, m, pas, i, L], μ⟩ T Q := by
  have := std.const_le
  -- while 0 < Place
  refine Ends.whileConst (Inv μ L m pas i) L binomPlace.blockCost ?start ?round ?done
    (by simp [binomPlace]; omega)
  case start => exact ⟨μ, rfl, fun j hj => by rw [if_neg (by omega), hrow j hj], .refl⟩
  case round =>
    intro r σ hr h
    have hplace := binomPlace_spec (P := P) (d := d) std hsp hi hw hr h
    obtain ⟨μ', rfl, -⟩ := h
    exact ⟨by light_side, by light_side, hplace⟩
  case done =>
    rintro _ ⟨μ', rfl, hcells, same⟩
    refine ⟨by light_side, by light_side, ?_⟩
    have hdone := done μ' (fun j hj => ?_) same
    · simpa using hdone
    · -- Entry 0 is 1 in every row.
      rw [hcells j hj, Nat.sub_self]
      split_ifs with hj0
      · rfl
      · rw [show j = 0 by omega, Nat.choose_zero_right, Nat.choose_zero_right]

/-! ## The loop over the rows -/

/-- The state before round i: the cells hold row i of the triangle. -/
def RowAt (μ : ℕ → ℤ) (L m pas i : ℕ) (σ : State) : Prop :=
  ∃ (p : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [L, m, pas, i, p], μ'⟩ ∧
    (∀ j ≤ L, μ' (pas + j) = (i.choose j : ℕ)) ∧ SameOutside μ μ' pas (L + 2)

/-- The time of one round of the loop over the rows. -/
def tRow (L : ℕ) : ℕ := 23 * L + 10

/-- **One round of the loop over the rows** turns row `i` of the triangle into row `i + 1`. -/
theorem binomRow_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space) (hi : i < L)
    (hw : ((2 ^ L : ℕ) : ℤ) ≤ lim.word) {σ : State} (h : RowAt μ L m pas i σ) :
    Ends lim P d binomRow σ (tRow L) (RowAt μ L m pas (i + 1)) := by
  obtain ⟨p, μ', rfl, hrow, same⟩ := h
  light_facts std
  unfold binomRow tRow
  -- Place := L
  light_set L
  refine Ends.next _ (binomInner_spec std hsp hi hw hrow ?_ le_rfl)
  intro μ'' hnew same'
  -- Row := Row + 1
  light_set (i + 1 : ℕ)
  exact ⟨_, _, rfl, hnew, same.trans same'⟩

/-- **Row 0** of the triangle is written: 1 followed by `L` zeros. -/
theorem binomFirst_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space)
    (done : ∀ σ, RowAt μ L m pas 0 σ → Q σ) (hT : 15 * L + 11 ≤ T) :
    Ends lim P d binomFirst ⟨frame [L, m, pas], μ⟩ T Q := by
  light_facts std
  -- mem[pas] := 1; Place := 1; while Place < L + 1
  light_store pas 1
  light_set (0 + 1 : ℕ)
  refine Ends.whileBlock
    (fun q σ => σ = ⟨frame [L, m, pas, 0, (q + 1 : ℕ)],
      wrote (Function.update μ pas 1) (pas + 1) (fun _ => 0) q⟩) L ?start ?round ?done
  case start =>
    rw [wrote_zero]
    rfl
  case round =>
    rintro q _ hq rfl
    have haddr : ((pas : ℤ) + ((q : ℤ) + 1)).toNat = pas + 1 + q := by omega
    -- mem[pas + Place] := 0; Place := Place + 1
    exact ⟨by light_side, by light_side, by light_side,
      by simp [update_frame_setLocal, ← wrote_succ, haddr]⟩
  case done =>
    rintro _ rfl
    refine ⟨by light_side, by light_side, done _ ⟨_, _, rfl, fun j hj => ?_,
      (SameOutside.refl.update ⟨by omega, by omega⟩ 1).trans
        ((sameOutside_wrote le_rfl).mono (by omega) (by omega))⟩⟩
    -- (0 choose 0) = 1, and (0 choose j + 1) = 0.
    cases j with
    | zero => rw [wrote_rest (Or.inl (by omega)), Nat.add_zero, Function.update_self]; rfl
    | succ j => rw [← Nat.add_assoc, Nat.add_right_comm, wrote_done (by omega)]; rfl

end Binom

variable {μ : ℕ → ℤ} {L m pas : ℕ}

/-- **binom** returns (L choose m) and changes no cell outside the L + 2 cells from pas. -/
theorem binom_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space) (hm : m ≤ L)
    (hw : ((2 ^ L : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d binomBody ⟨frame [L, m, pas], μ⟩ (30 * (L + 1) ^ 2) fun σ' =>
      σ'.loc 0 = (L.choose m : ℕ) ∧ SameOutside μ σ'.mem pas (L + 2) := by
  light_facts std
  -- Row 0.
  refine Ends.next _ (binomFirst_spec std hsp ?_ le_rfl) (by ring_nf; omega)
  intro σ hfirst
  -- while Row < L; the L rounds take L (23 L + 14) steps
  refine Ends.next _ (Ends.whileConst (RowAt μ L m pas) L (tRow L) hfirst ?round ?done le_rfl)
    (by simp [tRow]; ring_nf; omega)
  case round =>
    intro i σ hi h
    have hrow := binomRow_spec (P := P) (d := d) std hsp hi hw h
    obtain ⟨p, μ', rfl, -⟩ := h
    exact ⟨by light_side, by light_side, hrow⟩
  case done =>
    rintro _ ⟨p, μ', rfl, hrow, same⟩
    refine ⟨by light_side, by light_side, ?_⟩
    -- The result: local 0 := mem[pas + m]
    exact Ends.setTo (L.choose m : ℕ) ⟨by simp, same⟩
      (by light_side [hrow m hm]) (by simp [tRow]; ring_nf; omega)

/-- **The specification that the callers of binom assume.** -/
theorem binom_entry (std : Std lim) (hP : P[pBinom]? = some binomBody) {c : ℕ} (hc : 30 ≤ c) :
    BinomSpec lim P c :=
  fun _ _ _ _ hsp hm hw _ _ => .mono_const (.of_body hP (binom_spec std hsp hm hw)) hc

end Light.Sec2

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Tables of digits, by an odometer

The programs for Theorem 5 turn the number of a row or of a column into a string ("locate the output
strings", in the proof of Theorem 5), so they need the digits of these numbers in base 3 and in
base 4. digits(n, b, len, dst) writes, for every x < n, the len digits of x % b^len in base b, most
significant first, to the len cells from dst + x * len.  There is no division: row 0 is zero, and
row x + 1 is row x plus one, formed from the least significant digit on with a carry.

* The pure side: `carryInto b j x` is the carry into the place of weight b^j when 1 is added to x,
  defined as the routine computes it, and `placeDigit_succ` says that a place of x plus its carry,
  reduced if it reaches b, is the place of x + 1.
* `digitsPlace_spec` treats one place, `digitsInner_spec` one row, `digitsZero_spec` row 0, and
  `digits_spec` runs through the rows; `digits_entry` is the specification that the callers of the
  procedure assume.
-/


open ThreeSumApsp

namespace Light.Sec2

namespace Digits

/-! ## Adding 1 to a number, place by place -/

/-- The digit of weight b^j of x. -/
def placeDigit (b j x : ℕ) : ℕ := x / b ^ j % b

/-- The carry into the digit of weight b^j when 1 is added to x: 1 into the last place, and then 1
as long as the digit plus the carry reaches b. -/
def carryInto (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | j + 1, x => if placeDigit b j x + carryInto b j x < b then 0 else 1

/-- A digit is less than the base. -/
theorem placeDigit_lt {b : ℕ} (hb : 0 < b) (j x : ℕ) : placeDigit b j x < b :=
  Nat.mod_lt _ hb

/-- A carry is 0 or 1. -/
theorem carryInto_le_one (b j x : ℕ) : carryInto b j x ≤ 1 := by
  cases j with
  | zero => exact le_rfl
  | succ j =>
    rw [carryInto]
    split_ifs <;> omega

/-- Adding a carry c to q: the last digit of q grows by c, or becomes 0 and gives a carry. -/
theorem add_carry {b : ℕ} (hb : 0 < b) (q : ℕ) {c : ℕ} (hc : c ≤ 1) :
    (q + c) / b = q / b + (if q % b + c < b then 0 else 1) ∧
      (q + c) % b = if q % b + c < b then q % b + c else 0 := by
  have hlt : q % b < b := Nat.mod_lt q hb
  obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
  · simp [hlt]
  · split_ifs with h
    · exact Nat.succ_div_mod_of_lt h
    · exact Nat.succ_div_mod_of_eq (by omega)

/-- The digits of x + 1 from the place of weight b^j on are those of x plus the carry. -/
theorem succ_div_pow {b : ℕ} (hb : 0 < b) (j x : ℕ) :
    (x + 1) / b ^ j = x / b ^ j + carryInto b j x := by
  induction j with
  | zero => simp [carryInto]
  | succ j ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ih, (add_carry hb _ (carryInto_le_one b j x)).1,
      Nat.div_div_eq_div_mul]
    rfl

/-- **One place of the odometer.**  The digit of x + 1 is the digit of x plus the carry, or 0 if
this reaches b. -/
theorem placeDigit_succ {b : ℕ} (hb : 0 < b) (j x : ℕ) :
    placeDigit b j (x + 1) =
      if placeDigit b j x + carryInto b j x < b then placeDigit b j x + carryInto b j x else 0 := by
  rw [placeDigit, succ_div_pow hb, (add_carry hb _ (carryInto_le_one b j x)).2]
  rfl

/-- The digits below place len do not change when the number is reduced modulo b^len. -/
theorem mod_pow_div_mod (b c : ℕ) {j len : ℕ} (hj : j < len) :
    c % b ^ len / b ^ j % b = c / b ^ j % b := by
  obtain ⟨e, rfl⟩ : ∃ e, len = j + (e + 1) := ⟨len - j - 1, by omega⟩
  rw [Nat.pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self b e.succ_ne_zero)]

/-- The entry number q of the row of x. -/
theorem getElem_digitList {b len x q : ℕ} (hq : q < len)
    (h : q < (ThreeSumApsp.digitList b len (x % b ^ len)).length) :
    (ThreeSumApsp.digitList b len (x % b ^ len))[q] = placeDigit b (len - 1 - q) x := by
  simp [ThreeSumApsp.digitList, ThreeSumApsp.digit, placeDigit,
    mod_pow_div_mod b x (show len - 1 - q < len by omega)]

/-! ## The program -/

/-- The local variables of digits: Total = n, Base = b, Len = len, Dest = dst (the arguments); Row
is the number of the row being written, Cur its address and Prev the address of the row before it;
Place is the place, Carry the carry into it, and Digit the new digit. -/
abbrev Total : ℕ := 0
@[inherit_doc Total] abbrev Base : ℕ := 1
@[inherit_doc Total] abbrev Len : ℕ := 2
@[inherit_doc Total] abbrev Dest : ℕ := 3
@[inherit_doc Total] abbrev Row : ℕ := 4
@[inherit_doc Total] abbrev Cur : ℕ := 5
@[inherit_doc Total] abbrev Prev : ℕ := 6
@[inherit_doc Total] abbrev Place : ℕ := 7
@[inherit_doc Total] abbrev Carry : ℕ := 8
@[inherit_doc Total] abbrev Digit : ℕ := 9

end Digits

open Digits

variable {lim : Limits} {P : Program} {d : ℕ}

/-- One place of the new row: the digit of the row before it plus the carry, or 0 if this reaches
b; in the second case the carry stays 1. -/
def digitsPlace : Stmt :=
  .set Place (v Place -' k 1) ;;
  .set Digit (M (v Prev +' v Place) +' v Carry) ;;
  .ite (v Digit <' v Base) (
    .store (v Cur +' v Place) (v Digit) ;;
    .set Carry (k 0)) (
    .store (v Cur +' v Place) (k 0))

/-- The loop that forms one row from the row before it, from the last place on. -/
def digitsInner : Stmt := .while (k 0 <' v Place) digitsPlace

/-- One round of the loop over the rows. -/
def digitsRow : Stmt :=
  .set Place (v Len) ;;
  .set Carry (k 1) ;;
  digitsInner ;;
  .set Row (v Row +' k 1) ;;
  .set Prev (v Cur) ;;
  .set Cur (v Cur +' v Len)

/-- Row 0 is zero.  The place is not set at the beginning: local variables that are not arguments
start at 0. -/
def digitsZero : Stmt :=
  .while (v Place <' v Len) (
    .store (v Dest +' v Place) (k 0) ;;
    .set Place (v Place +' k 1))

/-- digits(n, b, len, dst). -/
def digitsBody : Stmt :=
  .ite (k 0 <' v Total) (
    digitsZero ;;
    .set Row (k 1) ;;
    .set Prev (v Dest) ;;
    .set Cur (v Dest +' v Len) ;;
    .while (v Row <' v Total) digitsRow) .skip

namespace Digits

/-! ## One row from the row before it -/

/-- The memory after r places of the row of y + 1 have been written to the len cells from cur, from
the last place on; no other cell has changed. -/
def Placed (μ : ℕ → ℤ) (b len cur y r : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ j < r, μ' (cur + (len - 1 - j)) = (placeDigit b j (y + 1) : ℕ)) ∧ SameOutside μ μ' cur len

/-- One more place. -/
theorem Placed.step {μ μ' : ℕ → ℤ} {b len cur y r : ℕ} (h : Placed μ b len cur y r μ')
    (hr : r < len) :
    Placed μ b len cur y (r + 1)
      (Function.update μ' (cur + (len - 1 - r)) (placeDigit b r (y + 1) : ℕ)) := by
  refine ⟨fun j hj => ?_, h.2.update ⟨by omega, by omega⟩ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · rw [Function.update_of_ne (by omega)]
    exact h.1 j hj
  · exact Function.update_self ..

/-- The state after r places: the place is len - r, and the carry is the carry into place r. -/
def Inv (μ : ℕ → ℤ) (n b len dst row cur prev y r : ℕ) (σ : State) : Prop :=
  ∃ (x : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [n, b, len, dst, row, cur, prev, (len - r : ℕ), carryInto b r y, x], μ'⟩ ∧
      Placed μ b len cur y r μ'

variable {μ : ℕ → ℤ} {n b len dst row cur prev y : ℕ} {T : ℕ} {Q : State → Prop}

/-- **One place** of the new row is written, and the carry into the next place is formed. -/
theorem digitsPlace_spec (std : Std lim) (hb : 2 ≤ b) (hbw : (b : ℤ) ≤ lim.word)
    (hcur : cur + len ≤ lim.space) (hprev : prev + len ≤ cur)
    (hrow : ∀ q < len, μ (prev + q) = (placeDigit b (len - 1 - q) y : ℕ)) {r : ℕ} (hr : r < len)
    {σ : State} (h : Inv μ n b len dst row cur prev y r σ) :
    Ends lim P d digitsPlace σ digitsPlace.blockCost
      (Inv μ n b len dst row cur prev y (r + 1)) := by
  obtain ⟨x, μ', rfl, hI⟩ := h
  light_facts std
  have hdigit := placeDigit_lt (show 0 < b by omega) r y
  have hcarry := carryInto_le_one b r y
  have hnew := placeDigit_succ (show 0 < b by omega) r y
  have hstep := hI.step hr
  rw [show len - 1 - r = len - (r + 1) by omega, hnew] at hstep
  -- The digit of the row before has not been overwritten.
  have hread : μ' (prev + (len - (r + 1))) = (placeDigit b r y : ℕ) := by
    rw [hI.2 _ (Or.inl (by omega)), hrow _ (by omega), show len - 1 - (len - (r + 1)) = r by omega]
  unfold digitsPlace
  -- Place := Place - 1; Digit := mem[Prev + Place] + Carry
  light_set (len - (r + 1) : ℕ)
  light_set (placeDigit b r y + carryInto b r y : ℕ) using hread
  -- if Digit < b
  refine Ends.iteLast (fun hc => ?_) fun hc => ?_
  · -- No carry out of this place: mem[Cur + Place] := Digit; Carry := 0
    have hlt : placeDigit b r y + carryInto b r y < b := by simp at hc; omega
    rw [if_pos hlt] at hstep
    refine Ends.storeToThen (cur + (len - (r + 1))) ((placeDigit b r y + carryInto b r y : ℕ) : ℤ)
      (Ends.setTo ((0 : ℕ) : ℤ) ⟨((placeDigit b r y + carryInto b r y : ℕ) : ℤ), _, ?_, hstep⟩)
    rw [carryInto, if_pos hlt]
    rfl
  · -- A carry out of this place, so the carry into it was 1 and stays: mem[Cur + Place] := 0
    have hlt : ¬ placeDigit b r y + carryInto b r y < b := by simp at hc; omega
    rw [if_neg hlt] at hstep
    refine Ends.storeTo (cur + (len - (r + 1))) ((0 : ℕ) : ℤ)
      ⟨((placeDigit b r y + carryInto b r y : ℕ) : ℤ), _, ?_, hstep⟩
    rw [carryInto, if_neg hlt, show carryInto b r y = 1 by omega]
    rfl

/-- **One row**: the loop over the places writes the row of y + 1 to the len cells from cur, from
the row of y in the len cells from prev. -/
theorem digitsInner_spec (std : Std lim) (hb : 2 ≤ b) (hbw : (b : ℤ) ≤ lim.word)
    (hcur : cur + len ≤ lim.space) (hprev : prev + len ≤ cur)
    (hrow : ∀ q < len, μ (prev + q) = (placeDigit b (len - 1 - q) y : ℕ)) {x₀ : ℤ}
    (done : ∀ (c x : ℤ) (μ' : ℕ → ℤ),
      (∀ q < len, μ' (cur + q) = (placeDigit b (len - 1 - q) (y + 1) : ℕ)) →
      SameOutside μ μ' cur len → Q ⟨frame [n, b, len, dst, row, cur, prev, 0, c, x], μ'⟩)
    (hT : 26 * len + 4 ≤ T) :
    Ends lim P d digitsInner ⟨frame [n, b, len, dst, row, cur, prev, len, 1, x₀], μ⟩ T Q := by
  have := std.const_le
  -- while 0 < Place
  refine Ends.whileConst (Inv μ n b len dst row cur prev y) len digitsPlace.blockCost ?start ?round
    ?done
    (by simp [digitsPlace]; omega)
  case start => exact ⟨x₀, μ, rfl, fun j hj => absurd hj (by omega), .refl⟩
  case round =>
    intro r σ hr h
    have hplace := digitsPlace_spec (P := P) (d := d) std hb hbw hcur hprev hrow hr h
    obtain ⟨x, μ', rfl, -⟩ := h
    exact ⟨by light_side, by light_side, hplace⟩
  case done =>
    rintro _ ⟨x, μ', rfl, hcells, same⟩
    refine ⟨by light_side, by light_side, ?_⟩
    have hdone := done (carryInto b len y) x μ' (fun q hq => ?_) same
    · simpa using hdone
    · rw [← hcells (len - 1 - q) (by omega), show len - 1 - (len - 1 - q) = q by omega]

/-! ## The loop over the rows -/

/-- The state after the rows 0, …, i have been written: they stand in the table, and no cell outside
the table has changed. -/
def RowsDone (μ : ℕ → ℤ) (n b len dst i : ℕ) (σ : State) : Prop :=
  ∃ (p c x : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [n, b, len, dst, (i + 1 : ℕ), (dst + (i + 1) * len : ℕ),
      (dst + i * len : ℕ), p, c, x], μ'⟩ ∧
    (∀ y < i + 1, ∀ q < len, μ' (dst + y * len + q) = (placeDigit b (len - 1 - q) y : ℕ)) ∧
    SameOutside μ μ' dst (n * len)

/-- The time of one round of the loop over the rows. -/
def tRow (len : ℕ) : ℕ := 26 * len + 18

/-- **One round of the loop over the rows** writes row `i + 1`, the digits of `i + 1`, from row
`i`. -/
theorem digitsRow_spec (std : Std lim) (hb : 2 ≤ b) (hbw : (b : ℤ) ≤ lim.word)
    (hsp : dst + n * len ≤ lim.space) (hnw : (n : ℤ) ≤ lim.word) {i : ℕ} (hi : i + 1 < n)
    {σ : State} (h : RowsDone μ n b len dst i σ) :
    Ends lim P d digitsRow σ (tRow len) (RowsDone μ n b len dst (i + 1)) := by
  obtain ⟨p, c, x, μ', rfl, hrows, same⟩ := h
  light_facts std
  have : (i + 1) * len + len ≤ n * len := Nat.mul_add_le_mul hi le_rfl
  have : (i + 1) * len = i * len + len := Nat.succ_mul i len
  unfold digitsRow tRow
  -- Place := len; Carry := 1
  light_set len
  light_set 1
  -- while 0 < Place
  refine Ends.next _ (digitsInner_spec (y := i) std hb hbw (by omega) (by omega)
    (fun q hq => hrows i (by omega) q hq) ?_ le_rfl)
  intro c' x' μ'' hnew same'
  -- Row := Row + 1; Prev := Cur; Cur := Cur + len
  light_set (i + 1 + 1 : ℕ)
  light_set (dst + (i + 1) * len : ℕ)
  light_set (dst + (i + 1 + 1) * len : ℕ) using Nat.succ_mul
  refine ⟨_, _, _, _, rfl, fun y hy q hq => ?_,
      same.trans (same'.mono (by omega) (by omega))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
  · -- An earlier row lies before the cells that were written.
    have : y * len + len ≤ (i + 1) * len := Nat.mul_add_le_mul hy le_rfl
    rw [same' _ (Or.inl (by omega))]
    exact hrows y hy q hq
  · exact hnew q hq

/-- **Row 0** is zero. -/
theorem digitsZero_spec (std : Std lim) (hsp : dst + len ≤ lim.space)
    (done : Q ⟨frame [n, b, len, dst, 0, 0, 0, len], wrote μ dst (fun _ => 0) len⟩)
    (hT : 13 * len + 4 ≤ T) :
    Ends lim P d digitsZero ⟨frame [n, b, len, dst], μ⟩ T Q := by
  light_facts std
  -- while Place < len
  refine Ends.whileBlock (fun q σ => σ =
    ⟨frame [n, b, len, dst, 0, 0, 0, q], wrote μ dst (fun _ => 0) q⟩) len ?start ?round ?done
  case start =>
    -- The place starts at 0.
    rw [wrote_zero, ← frame_append_zeros _ 4]
    rfl
  case round =>
    rintro q _ hq rfl
    -- mem[dst + Place] := 0; Place := Place + 1
    exact ⟨by light_side, by light_side, by light_side,
      by simp [update_frame_setLocal, ← wrote_succ]⟩
  case done =>
    rintro _ rfl
    exact ⟨by light_side, by light_side, done⟩

end Digits

variable {μ : ℕ → ℤ} {n b len dst : ℕ}

/-- **digits** writes the table of digits and changes nothing else. -/
theorem digits_spec (std : Std lim) (hsp : dst + n * len ≤ lim.space) (hb : 2 ≤ b)
    (hbw : (b : ℤ) ≤ lim.word) (hnw : (n : ℤ) ≤ lim.word) :
    Ends lim P d digitsBody ⟨frame [n, b, len, dst], μ⟩ (60 * ((n + 1) * (len + 1))) fun σ' =>
      (∀ x < n, SegN σ'.mem (dst + x * len) (ThreeSumApsp.digitList b len (x % b ^ len))) ∧
        SameOutside μ σ'.mem dst (n * len) := by
  light_facts std
  -- if 0 < n
  refine Ends.iteLast (fun hpos => ?_) fun hzero => Ends.skip
    ⟨fun x hx => absurd hx (by simp at hzero; omega), .refl⟩
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by simp at hpos; omega⟩
  have hlen : (t + 1) * len = t * len + len := Nat.succ_mul t len
  -- Row 0.
  refine Ends.next _ (digitsZero_spec std (by omega) ?_ le_rfl) (by simp; ring_nf; omega)
  -- Row := 1; Prev := dst; Cur := dst + len, written as the invariant at i = 0 has them
  light_set (0 + 1 : ℕ)
  light_set (dst + 0 * len : ℕ)
  light_set (dst + (0 + 1) * len : ℕ)
  -- while Row < n; the n - 1 rounds take (n - 1) (26 len + 22) steps
  refine Ends.whileConst (RowsDone μ (t + 1) b len dst) t (tRow len) ?start ?round ?done
    (by simp [tRow]; ring_nf; omega)
  case start =>
    refine ⟨len, 0, 0, wrote μ dst (fun _ => 0) len, ?_, fun y hy q hq => ?_,
      sameOutside_wrote (hlen ▸ Nat.le_add_left ..)⟩
    · -- The carry and the digit start at 0.
      rw [← frame_append_zeros _ 2]
      rfl
    · obtain rfl : y = 0 := by omega
      rw [Nat.zero_mul, Nat.add_zero, wrote_done hq]
      simp [placeDigit]
  case round =>
    intro i σ hi h
    have hrow := digitsRow_spec (P := P) (d := d) std hb hbw hsp hnw (by omega) h
    obtain ⟨p, c, x, μ', rfl, -⟩ := h
    exact ⟨by light_side, by light_side, hrow⟩
  case done =>
    rintro _ ⟨p, c, x, μ', rfl, hrows, same⟩
    refine ⟨by light_side, by light_side, fun y hy q hq => ?_, same⟩
    have hq' : q < len := by simpa [ThreeSumApsp.digitList] using hq
    rw [List.getElem_map, getElem_digitList hq']
    exact hrows y hy q hq'

/-- **The specification that the callers of digits assume.** -/
theorem digits_entry (std : Std lim) (hP : P[pDigits]? = some digitsBody) {c : ℕ} (hc : 60 ≤ c) :
    DigitsSpec lim P c :=
  fun _ _ _ _ _ hsp hb hbw hnw _ _ => .mono_const (.of_body hP (digits_spec std hsp hb hbw hnw)) hc

end Light.Sec2

end

section



/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The table of subsets: how a row is made from the row before it

Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
of the grid, the same in every tile."  The programs keep them in a table.  Row number `s` of the
table is the mask `Spec.unrank L m s`, as `L` cells 1 and 0 (`bit`).  No program occurs here.

* The first row is `m` ones followed by zeros (`bit_unrank_zero`).
* Two consecutive masks are `pre 1 0 0^a 1^b` and `pre 0 1 1^b 0^a` (`Spec.unrank_succ_shape`).  So
  one pass from the end of the old row finds `b` and the length of `pre`: `scanAt` is the state of
  this scan after a number of rounds, and `scanAt_shape` is what it has found after all rounds.
* A second pass writes the new row: `newCell` is the cell that it writes (`bit_unrank_succ`), and
  the numbers that it computes on the way are small (`scanAt_fits`).
-/


namespace ThreeSumApsp.Spec.Subsets

/-- A truth value as a cell. -/
def bit (b : Bool) : ℤ := if b then 1 else 0

/-- Row 0 of the table is `m` ones followed by `L - m` zeros. -/
theorem bit_unrank_zero {L m q : ℕ} (hm : m ≤ L) (hq : q < L) :
    bit ((Spec.unrank L m 0).getD q false) = if q < m then 1 else 0 := by
  rw [Spec.unrank_zero hm]
  grind [bit]

/-- The entries of a list of the form `pre ++ x :: y :: (u^a ++ v^b)`. -/
theorem getD_shape (pre : List Bool) (x y u v : Bool) (a b q : ℕ) :
    (pre ++ x :: y :: (List.replicate a u ++ List.replicate b v)).getD q false =
      if q < pre.length then pre.getD q false
      else if q = pre.length then x
      else if q = pre.length + 1 then y
      else if q < pre.length + 2 + a then u
      else if q < pre.length + 2 + a + b then v else false := by
  grind

/-! ## The backward scan -/

/-- The state of the scan: the phase (0 while the ones at the end of the row are counted, 1 while
the zeros before them are passed, 2 when the 1 before these zeros has been found), the number of
ones at the end of the row, and the position of the 1 that was found.  The three fields are the
contents of three local variables of the routine, so they are integers, and `scanStep` and `newCell`
compare them by `<`, the comparison of the language. -/
structure Scan where
  /-- The phase: 0, 1 or 2. -/
  phase : ℤ
  /-- The number of ones at the end of the row. -/
  ones : ℤ
  /-- The position of the last 1 that is followed by a 0. -/
  pos : ℤ

/-- The result of a scan fits into a row of `L` cells: the position `p` and the number `b` of ones
are natural numbers with `p + 2 + b ≤ L`. -/
def Scan.Fits (S : Scan) (L : ℕ) : Prop := 0 ≤ S.pos ∧ 0 ≤ S.ones ∧ S.pos + 2 + S.ones ≤ L

/-- One round of the scan: `x` is the cell that is read, and `q` its position. -/
def scanStep (x q : ℤ) (S : Scan) : Scan :=
  if S.phase < 1 then (if x < 1 then { S with phase := 1 } else { S with ones := S.ones + 1 })
  else if S.phase < 2 then (if x < 1 then S else { S with phase := 2, pos := q })
  else S

/-- The state of the scan of a row of length `L` after `j` rounds. -/
def scanAt (row : ℕ → ℤ) (L : ℕ) : ℕ → Scan
  | 0 => ⟨0, 0, 0⟩
  | j + 1 => scanStep (row (L - 1 - j)) ((L : ℤ) - 1 - (j : ℤ)) (scanAt row L j)

/-- One round counts at most one more 1. -/
theorem scanStep_ones (x q : ℤ) (S : Scan) :
    (scanStep x q S).ones = S.ones ∨ (scanStep x q S).ones = S.ones + 1 := by
  unfold scanStep
  split_ifs <;> simp

/-- After `j` rounds at most `j` ones have been counted. -/
theorem scanAt_ones_le (row : ℕ → ℤ) (L j : ℕ) :
    0 ≤ (scanAt row L j).ones ∧ (scanAt row L j).ones ≤ j := by
  induction j with
  | zero => simp [scanAt]
  | succ j ih =>
    have := scanStep_ones (row (L - 1 - j)) ((L : ℤ) - 1 - (j : ℤ)) (scanAt row L j)
    rw [scanAt]
    push_cast
    omega

section shape
variable {pre : List Bool} {a b L : ℕ} {row : ℕ → ℤ} (hL : L = pre.length + 2 + a + b)
  (hrow : ∀ q < L, row q =
    bit ((pre ++ true :: false :: (List.replicate a false ++ List.replicate b true)).getD q false))
include hL hrow

/-- The cell that round `j` reads: 1 for the `b` ones at the end of the row, 0 for the `a + 1` zeros
before them, and 1 for the cell before these. -/
theorem row_sub (j : ℕ) (hj : j ≤ b + a + 1) :
    row (L - 1 - j) = if j < b then 1 else if j < b + a + 1 then 0 else 1 := by
  rw [hrow _ (by omega), getD_shape]
  grind [bit]

/-- Phase 0: the `b` ones at the end of the row are counted. -/
theorem scanAt_count (j : ℕ) (hj : j ≤ b) : scanAt row L j = ⟨0, j, 0⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [scanAt, ih (by omega), row_sub hL hrow j (by omega), if_pos (by omega)]
    simp [scanStep]

/-- Phase 1: the `a + 1` zeros before the ones are passed. -/
theorem scanAt_pass (i : ℕ) (hi : i ≤ a) : scanAt row L (b + 1 + i) = ⟨1, b, 0⟩ := by
  induction i with
  | zero =>
    rw [Nat.add_zero, scanAt, scanAt_count hL hrow b le_rfl, row_sub hL hrow b (by omega),
      if_neg (by omega), if_pos (by omega)]
    simp [scanStep]
  | succ i ih =>
    rw [← Nat.add_assoc, scanAt, ih (by omega), row_sub hL hrow _ (by omega), if_neg (by omega),
      if_pos (by omega)]
    simp [scanStep]

/-- Phase 2: the 1 before the `a + 1` zeros is found, at the position after `pre`, and from then on
the state stays as it is. -/
theorem scanAt_found (i : ℕ) (hi : i ≤ pre.length) :
    scanAt row L (b + 1 + a + 1 + i) = ⟨2, b, pre.length⟩ := by
  induction i with
  | zero =>
    rw [Nat.add_zero, scanAt, scanAt_pass hL hrow a le_rfl, row_sub hL hrow _ (by omega),
      if_neg (by omega), if_neg (by omega),
      show (L : ℤ) - 1 - ((b + 1 + a : ℕ) : ℤ) = pre.length by omega]
    simp [scanStep]
  | succ i ih =>
    rw [← Nat.add_assoc, scanAt, ih (by omega)]
    rfl

/-- The scan of a row of the shape `pre 1 0 0^a 1^b` finds `b` and the length of `pre`. -/
theorem scanAt_shape : scanAt row L L = ⟨2, b, pre.length⟩ := by
  rw [← scanAt_found hL hrow pre.length le_rfl]
  congr 1
  omega

end shape

/-! ## The writing pass -/

/-- The cell number `q` of the new row, from the cell of the old row and the result of the scan. -/
def newCell (S : Scan) (old q : ℤ) : ℤ :=
  if q < S.pos then old else if q < S.pos + 1 then 0 else if q < S.pos + 2 + S.ones then 1 else 0

section next
variable {L m s : ℕ} (hs : s + 1 < L.choose m) {row : ℕ → ℤ}
  (hrow : ∀ q < L, row q = bit ((Spec.unrank L m s).getD q false))
include hs hrow

/-- **From one row to the next.**  If row number `s` has a successor, the cells of row `s + 1` are
given by `newCell`, from the cells of row `s` and the result of its scan. -/
theorem bit_unrank_succ {q : ℕ} (hq : q < L) :
    bit ((Spec.unrank L m (s + 1)).getD q false) = newCell (scanAt row L L) (row q) q := by
  obtain ⟨pre, a, b, hL, hthis, hnext⟩ := Spec.unrank_succ_shape hs
  rw [hthis] at hrow
  rw [scanAt_shape hL hrow, hrow q hq, hnext, getD_shape, getD_shape, newCell]
  dsimp only
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The result of the scan of a row that has a successor fits into a row. -/
theorem scanAt_fits : (scanAt row L L).Fits L := by
  obtain ⟨pre, a, b, hL, hthis, -⟩ := Spec.unrank_succ_shape hs
  rw [hthis] at hrow
  rw [scanAt_shape hL hrow, Scan.Fits]
  dsimp only
  omega

end next

end ThreeSumApsp.Spec.Subsets

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The table of subsets

Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
of the grid, the same in every tile."  Section 2.4.4 counts the time to "list the K₀² subsets".
subsets(L, m, KK, mask), which is called with KK = K₀², writes the first KK masks of the enumeration
`Spec.unrank`, one after the other, as 0/1 cells from mask.  Row 0 is m ones followed by zeros
(`firstRow_spec`).  Each further row is made from the row before it: one pass from the end of the
old row finds the last 1 that is followed by a 0 (`scan_spec`), and one pass writes the new row
(`write_spec`).  There is no arithmetic on the entries, and a row takes O(L) steps.  What the two
passes compute is described without a program by `scanAt` and `newCell`, with the facts
`bit_unrank_succ` and `scanAt_fits`; here each pass is connected with this description,
`tableRow_spec` treats one row, and `subsetTable_spec` runs through the rows.  `subsets_entry` is
the specification that the callers of the procedure assume.
-/


open ThreeSumApsp.Spec.Subsets

namespace Light.Sec2.Subsets

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

/-- The local variables of subsets: Levels = L, Size = m, Rows = KK, Table = mask (the arguments);
Row is the number of the current row and Addr its address; Phase, Ones and Pos are the state of the
scan (phase, number of ones at the end, position found); Cell is the counter of the inner loops. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Size : ℕ := 1
@[inherit_doc Levels] abbrev Rows : ℕ := 2
@[inherit_doc Levels] abbrev Table : ℕ := 3
@[inherit_doc Levels] abbrev Row : ℕ := 4
@[inherit_doc Levels] abbrev Addr : ℕ := 5
@[inherit_doc Levels] abbrev Phase : ℕ := 6
@[inherit_doc Levels] abbrev Ones : ℕ := 7
@[inherit_doc Levels] abbrev Pos : ℕ := 8
@[inherit_doc Levels] abbrev Cell : ℕ := 9

/-- One cell of the first row: 1 for the first m cells, then 0. -/
def firstRowRound : Stmt :=
  .ite (v Cell <' v Size) (.store (v Addr +' v Cell) (k 1)) (.store (v Addr +' v Cell) (k 0))

/-- The first row: m ones, then zeros. -/
def firstRowLoop : Stmt := .for Cell (v Levels) firstRowRound

/-- One round of the scan: the cell number Cell from the end of the row before the current one. -/
def scanRound : Stmt :=
  .ite (v Phase <' k 1)
    (.ite (M (v Addr -' k 1 -' v Cell) <' k 1) (.set Phase (k 1)) (.set Ones (v Ones +' k 1)))
    (.ite (v Phase <' k 2)
      (.ite (M (v Addr -' k 1 -' v Cell) <' k 1) .skip
        (.set Phase (k 2) ;; .set Pos (v Levels -' k 1 -' v Cell)))
      .skip)

/-- The scan of the row before the current one, from its end. -/
def scanLoop : Stmt :=
  .set Phase (k 0) ;; .set Ones (k 0) ;; .set Pos (k 0) ;; .for Cell (v Levels) scanRound

/-- One cell of the new row, from the row before it and the result of the scan. -/
def writeRound : Stmt :=
  .ite (v Cell <' v Pos) (.store (v Addr +' v Cell) (M (v Addr -' v Levels +' v Cell)))
    (.ite (v Cell <' v Pos +' k 1) (.store (v Addr +' v Cell) (k 0))
      (.ite (v Cell <' v Pos +' k 2 +' v Ones) (.store (v Addr +' v Cell) (k 1))
        (.store (v Addr +' v Cell) (k 0))))

/-- The new row, from the row before it and the result of the scan. -/
def writeLoop : Stmt := .for Cell (v Levels) writeRound

/-- A further row, from the row before it. -/
def nextRow : Stmt := scanLoop ;; writeLoop

/-- One round of the loop over the rows. -/
def tableRow : Stmt :=
  .ite (v Row <' k 1) firstRowLoop nextRow ;;
  .set Row (v Row +' k 1) ;; .set Addr (v Addr +' v Levels)

/-- subsets(L, m, KK, mask). -/
def subsetTableBody : Stmt :=
  .set Row (k 0) ;; .set Addr (v Table) ;; .while (v Row <' v Rows) tableRow

/-! ## The three passes -/

/-- The list of the local variables. -/
abbrev locals (L m KK mask s a : ℕ) (S : Scan) (j : ℤ) : List ℤ :=
  [L, m, KK, mask, s, a, S.phase, S.ones, S.pos, j]

/-- The row of L cells that ends just before the address a. -/
abbrev prevRow (μ : ℕ → ℤ) (a L : ℕ) : ℕ → ℤ := fun q => μ (a - L + q)

/-- The row that the writing pass forms from the row before the address a and the result S of its
scan. -/
abbrev newRow (μ : ℕ → ℤ) (a L : ℕ) (S : Scan) : ℕ → ℤ := fun r => newCell S (prevRow μ a L r) r

variable {μ : ℕ → ℤ} {L m KK mask s a : ℕ} {S : Scan} {j₀ : ℤ} {T : ℕ} {Q : State → Prop}

/-- **The first row**: the pass writes m ones and then zeros to the L cells from a. -/
theorem firstRow_spec (std : Std lim) (ha : a + L ≤ lim.space)
    (done : Q ⟨frame (locals L m KK mask s a S L), wrote μ a (fun r => if r < m then 1 else 0) L⟩)
    (hT : 17 * L + 6 ≤ T) :
    Ends lim P d firstRowLoop ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q := by
  light_facts std
  -- for Cell < L
  refine Ends.forFrame (fun j μ' => μ' = wrote μ a (fun r => if r < m then 1 else 0) j) L
    wrote_zero.symm ?round (fun μ' h => h ▸ done) (hT := by simp [firstRowRound]; omega)
  rintro j _ hj rfl
  unfold firstRowRound
  -- if Cell < m then mem[Addr + Cell] := 1 else mem[Addr + Cell] := 0
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
  · light_store (a + j) 1
    exact ⟨rfl, by rw [← wrote_succ, if_pos (by simpa using hc)]⟩
  · light_store (a + j) 0
    exact ⟨rfl, by rw [← wrote_succ, if_neg (by simpa using hc)]⟩

/-- One round of the scan does to the local variables what `scanStep` says of the cell number j from
the end of the row of L cells that ends just before the address a. -/
theorem scanRound_runs (std : Std lim) (hLa : L ≤ a) (ha : a ≤ lim.space) {j : ℕ} (hj : j < L)
    (hones : 0 ≤ S.ones ∧ S.ones ≤ j) :
    scanRound.Runs lim ⟨frame (locals L m KK mask s a S j), μ⟩ fun σ' => σ' =
      ⟨frame (locals L m KK mask s a (scanStep (μ (a - 1 - j)) ((L : ℤ) - 1 - j) S) j), μ⟩ := by
  light_facts std
  have haddr : ((a : ℤ) - 1 - j).toNat = a - 1 - j := by omega
  unfold scanRound scanStep
  by_cases hcount : S.phase < 1
  · -- Phase 0: a zero ends the counting, a one is counted.
    rw [if_pos hcount]
    refine .ite_pos ?_
    by_cases hx : μ (a - 1 - j) < 1
    · rw [if_pos hx]
      exact .ite_pos ⟨by light_side, by simp [update_frame_setLocal]⟩ (by simpa [haddr] using hx)
    · rw [if_neg hx]
      exact .ite_neg ⟨by light_side, by simp [update_frame_setLocal]⟩ (by simpa [haddr] using hx)
  · rw [if_neg hcount]
    refine .ite_neg ?_
    by_cases hpass : S.phase < 2
    · -- Phase 1: a zero is passed, a one is what the scan looks for.
      rw [if_pos hpass]
      refine .ite_pos ?_
      by_cases hx : μ (a - 1 - j) < 1
      · rw [if_pos hx]
        exact .ite_pos ⟨trivial, rfl⟩ (by simpa [haddr] using hx)
      · rw [if_neg hx]
        exact .ite_neg ⟨by light_side, by simp [update_frame_setLocal]⟩ (by simpa [haddr] using hx)
    · -- Phase 2: nothing is left to do.
      rw [if_neg hpass]
      exact .ite_neg ⟨trivial, rfl⟩

/-- **The scan** of the row of L cells that ends just before the address a changes no cell and
leaves its result in the local variables. -/
theorem scan_spec (std : Std lim) (hLa : L ≤ a) (ha : a ≤ lim.space)
    (done : Q ⟨frame (locals L m KK mask s a (scanAt (prevRow μ a L) L L) L), μ⟩)
    (hT : 33 * L + 12 ≤ T) :
    Ends lim P d scanLoop ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q := by
  light_facts std
  -- Phase := 0; Ones := 0; Pos := 0
  light_set 0
  light_set 0
  light_set 0
  -- for Cell < L
  refine Ends.for (fun j σ =>
      σ = ⟨frame (locals L m KK mask s a (scanAt (prevRow μ a L) L j) j), μ⟩)
    L _ ?start (fun j σ hj _ hσ => Ends.block ?round le_rfl) ?done ?bound
    (hT := by simp [scanRound]; omega)
  case start => simp [update_frame_setLocal, scanAt]
  case round =>
    subst hσ
    refine (scanRound_runs std hLa ha hj (scanAt_ones_le _ L j)).mono ?_
    rintro _ rfl
    rw [scanAt, prevRow, show a - L + (L - 1 - j) = a - 1 - j by omega]
    simp [update_frame_setLocal]
  case done => exact fun _ _ h => h ▸ done
  case bound => exact fun j _ _ _ h => h ▸ by light_side

/-- **The writing pass** writes the new row to the L cells from a, from the row of L cells before
it and the result S of the scan. -/
theorem write_spec (std : Std lim) (hLa : L ≤ a) (ha : a + L ≤ lim.space)
    (hS : S.Fits L) (done : Q ⟨frame (locals L m KK mask s a S L), wrote μ a (newRow μ a L S) L⟩)
    (hT : 31 * L + 6 ≤ T) :
    Ends lim P d writeLoop ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q := by
  light_facts std
  unfold Scan.Fits at hS
  -- for Cell < L
  refine Ends.forFrame (fun j μ' => μ' = wrote μ a (newRow μ a L S) j) L wrote_zero.symm
    ?round (fun μ' h => h ▸ done) (hT := by simp [writeRound]; omega)
  rintro j _ hj rfl
  -- The cell of the old row has not been overwritten.
  have haddr : ((a : ℤ) - L + j).toNat = a - L + j := by omega
  have hold : wrote μ a (newRow μ a L S) j (a - L + j) = μ (a - L + j) :=
    wrote_rest (Or.inl (by omega))
  unfold writeRound
  rw [← wrote_succ, newRow, newCell]
  -- if Cell < Pos then mem[Addr + Cell] := mem[Addr - L + Cell] else if Cell < Pos + 1 then 0
  -- else if Cell < Pos + 2 + Ones then 1 else 0: the four cases of newCell
  refine Ends.iteLast (fun c₁ => ?_) fun c₁ => Ends.iteLast (fun c₂ => ?_) fun c₂ =>
    Ends.iteLast (fun c₃ => ?_) fun c₃ => ?_
  · light_store (a + j) (μ (a - L + j)) using haddr, hold
    exact ⟨rfl, by rw [if_pos (by simpa using c₁)]⟩
  · light_store (a + j) 0
    exact ⟨rfl, by rw [if_neg (by simpa using c₁), if_pos (by simpa using c₂)]⟩
  · light_store (a + j) 1
    exact ⟨rfl, by
      rw [if_neg (by simpa using c₁), if_neg (by simpa using c₂), if_pos (by simpa using c₃)]⟩
  · light_store (a + j) 0
    exact ⟨rfl, by
      rw [if_neg (by simpa using c₁), if_neg (by simpa using c₂), if_neg (by simpa using c₃)]⟩

/-- **A further row**: the two passes write the new row to the L cells from a, from the row of L
cells before it, if the result of the scan leaves room. -/
theorem nextRow_spec (std : Std lim) (hLa : L ≤ a) (ha : a + L ≤ lim.space)
    (hroom : (scanAt (prevRow μ a L) L L).Fits L)
    (done : Q ⟨frame (locals L m KK mask s a (scanAt (prevRow μ a L) L L) L),
      wrote μ a (newRow μ a L (scanAt (prevRow μ a L) L L)) L⟩)
    (hT : 64 * L + 18 ≤ T) :
    Ends lim P d nextRow ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q :=
  Ends.next _ (scan_spec std hLa (by omega) (write_spec std hLa ha hroom done (by omega)) le_rfl)

/-! ## The loop over the rows -/

/-- The state before row number s is written: the rows before it stand in the table, and no cell
outside the table has changed. -/
def RowsDone (μ : ℕ → ℤ) (L m KK mask s : ℕ) (σ : State) : Prop :=
  ∃ (S : Scan) (j : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame (locals L m KK mask s (mask + s * L) S j), μ'⟩ ∧
    (∀ t < s, SegB μ' (mask + t * L) (Spec.unrank L m t)) ∧ SameOutside μ μ' mask (KK * L)

/-- The time of one round of the loop over the rows. -/
def tRow (L : ℕ) : ℕ := 64 * L + 30

/-- The end of a round: row number s has been written, and the number and the address of the row
move on. -/
theorem rowDone_spec (std : Std lim) (hmask : mask + KK * L ≤ lim.space)
    (hKK : (KK : ℤ) ≤ lim.word) (hs : s < KK) {μ' : ℕ → ℤ} {f : ℕ → ℤ} {j : ℤ}
    (hrows : ∀ t < s, SegB μ' (mask + t * L) (Spec.unrank L m t))
    (same : SameOutside μ μ' mask (KK * L))
    (hf : ∀ r < L, f r = bit ((Spec.unrank L m s).getD r false))
    (hT : 8 ≤ T := by light_time) :
    Ends lim P d (.set Row (v Row +' k 1) ;; .set Addr (v Addr +' v Levels))
      ⟨frame (locals L m KK mask s (mask + s * L) S j), wrote μ' (mask + s * L) f L⟩ T
      (RowsDone μ L m KK mask (s + 1)) := by
  light_facts std
  have : s * L + L ≤ KK * L := Nat.mul_add_le_mul hs le_rfl
  -- Row := Row + 1; Addr := Addr + L
  light_set (s + 1 : ℕ)
  light_set (mask + (s + 1) * L : ℕ) using Nat.succ_mul
  refine ⟨S, j, _, rfl, fun t ht => ?_,
      same.trans ((sameOutside_wrote le_rfl).mono (by omega) (by omega))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
  · -- An earlier row lies before the cells that were written.
    have : t * L + L ≤ s * L := Nat.mul_add_le_mul ht le_rfl
    refine Seg.of_sameOutside (hrows t ht) (sameOutside_wrote le_rfl) (Or.inl ?_)
    rw [List.length_map, Spec.length_unrank]
    omega
  · -- The new row.
    intro r hr
    rw [List.length_map, Spec.length_unrank] at hr
    rw [wrote_done hr, hf r hr, List.getElem_map,
      List.getD_eq_getElem _ _ (by rwa [Spec.length_unrank])]
    rfl

/-- **One round of the loop over the rows** writes row number `s`, the mask number `s`. -/
theorem tableRow_spec (std : Std lim) (hmask : mask + KK * L ≤ lim.space) (hm : m ≤ L)
    (hKK : KK ≤ L.choose m) (hKL : ((KK + L : ℕ) : ℤ) ≤ lim.word) (hs : s < KK) {σ : State}
    (h : RowsDone μ L m KK mask s σ) :
    Ends lim P d tableRow σ (tRow L) (RowsDone μ L m KK mask (s + 1)) := by
  obtain ⟨S, j, μ', rfl, hrows, same⟩ := h
  light_facts std
  push_cast at hKL
  have hroom : s * L + L ≤ KK * L := Nat.mul_add_le_mul hs le_rfl
  unfold tableRow tRow
  -- if Row < 1
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · -- The first row.
    obtain rfl : s = 0 := by simp at hc; omega
    refine Ends.next _ (firstRow_spec std (by omega) ?_ le_rfl)
    exact rowDone_spec std hmask (by omega) hs hrows same fun r hr => (bit_unrank_zero hm hr).symm
  · -- A further row, from the row before it.
    obtain ⟨p, rfl⟩ : ∃ p, s = p + 1 := ⟨s - 1, by simp at hc; omega⟩
    have hsucc : (p + 1) * L = p * L + L := Nat.succ_mul p L
    have hprev : ∀ q < L, prevRow μ' (mask + (p + 1) * L) L q
        = bit ((Spec.unrank L m p).getD q false) := fun q hq => by
      rw [prevRow, show mask + (p + 1) * L - L + q = mask + p * L + q by omega]
      exact SegB.get (hrows p (by omega)) (by rwa [Spec.length_unrank])
    have hnext : p + 1 < L.choose m := by omega
    refine Ends.next _ (nextRow_spec std (by omega) (by omega) (scanAt_fits hnext hprev) ?_ le_rfl)
    exact rowDone_spec std hmask (by omega) hs hrows same fun r hr =>
      (bit_unrank_succ hnext hprev hr).symm

/-- **subsets** writes the table and changes nothing else. -/
theorem subsetTable_spec (std : Std lim) (hmask : mask + KK * L ≤ lim.space) (hm : m ≤ L)
    (hKK : KK ≤ L.choose m) (hKL : ((KK + L : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d subsetTableBody ⟨frame [L, m, KK, mask], μ⟩ (64 * ((KK + 1) * (L + 1))) fun σ' =>
      (∀ s < KK, SegB σ'.mem (mask + s * L) (Spec.unrank L m s)) ∧
        SameOutside μ σ'.mem mask (KK * L) := by
  light_facts std
  -- Row := 0; Addr := mask
  light_set 0
  light_set mask
  -- while Row < KK; the KK rounds take KK (64 L + 34) steps
  refine Ends.whileConst (RowsDone μ L m KK mask) KK (tRow L) ?start ?round ?done
    (by simp [tRow]; ring_nf; omega)
  case start =>
    refine ⟨⟨0, 0, 0⟩, 0, μ, ?_, fun t ht => absurd ht (by omega), .refl⟩
    -- The state of the scan and the counter of the inner loops start at 0.
    simp only [setLocal, Nat.zero_mul, Nat.add_zero]
    rw [← frame_append_zeros _ 4]
    rfl
  case round =>
    intro s σ hs h
    have hrow := tableRow_spec (P := P) (d := d) std hmask hm hKK hKL hs h
    obtain ⟨S, j, μ', rfl, -⟩ := h
    push_cast at hKL
    exact ⟨by light_side, by light_side, hrow⟩
  case done =>
    rintro _ ⟨S, j, μ', rfl, hrows, same⟩
    push_cast at hKL
    exact ⟨by light_side, by light_side, hrows, same⟩

end Light.Sec2.Subsets

namespace Light.Sec2

open ThreeSumApsp Subsets

variable {lim : Limits} {P : Program}

/-- **The specification that the callers of subsets assume.** -/
theorem subsets_entry (std : Std lim) (hP : P[pSubsets]? = some subsetTableBody) {c : ℕ}
    (hc : 64 ≤ c) : SubsetsSpec lim P c :=
  fun _ _ _ _ _ hmask hm hKK hKL _ _ =>
    .mono_const (.of_body hP (subsetTable_spec std hmask hm hKK hKL)) hc

end Light.Sec2

end




/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Three routines of the library, as their callers see them

The programs for Theorem 5 call their procedures by number, and a caller assumes a specification of
the procedure that does not name its body: PowSpec for the tables of powers, FillSpec for filling a
segment, SqrtSpec for the square root.  Each follows from the specification of the routine in the
library; pow first puts its arguments in the order of the library's routine.
-/


namespace Light.Sec2

variable {lim : Limits} {P : Program} {c : ℕ}

/-! ## The tables of powers -/

/-- pow(b, n, dst): the arguments are put in the order of powTable(dst, n + 1, b), whose body
follows.  Local 5 is a temporary. -/
def powBody : Stmt :=
  .set 5 (v 0) ;;
  .set 0 (v 2) ;;
  .set 2 (v 5) ;;
  .set 1 (v 1 +' k 1) ;;
  powTableBody

/-- **pow(b, n, dst)** writes the powers b^0, …, b^n to the cells from dst, within 35 (n + 1) steps.
-/
theorem pow_entry (std : Std lim) (hP : P[pPow]? = some powBody) (hc : 35 ≤ c) :
    PowSpec lim P c := by
  intro b n dst μ hdst1 hdst hb hpow d _
  have hw := std.space_le
  have := std.const_le
  refine .mono_const (.of_body hP ?_) hc
  -- The arguments b, n, dst become dst, n + 1, b.
  light_set b
  light_set dst
  light_set b
  light_set (n + 1 : ℕ)
  refine (powTable_ends (dst := dst) (L := n + 1) (b := b) 0 0 [b] hw hdst fun j hj => ?_).mono
    (by simp [powTableTime]; omega) fun _ h => h
  exact le_trans (by exact_mod_cast Nat.pow_le_pow_right hb hj) hpow

/-! ## Filling a segment -/

/-! ## The square root -/

/-- **sqrt(K)** returns ⌊√K⌋, within 18 (⌊√K⌋ + 1) steps. -/
theorem sqrt_entry (hP : P[pSqrt]? = some sqrtBody) (hc : 18 ≤ c) : SqrtSpec lim P c :=
  fun _ μ hw _ _ =>
    ((sqrt_meets hP μ (by push_cast at hw ⊢; omega)).mono_time (by simp; omega)).mono_const hc



open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-- A coefficient as an expression: 1, 0, or 0 - 1. -/
def signExpr (x : ℤ) : Expr := if x = 1 then k 1 else if x = 0 then k 0 else k 0 -' k 1

/-- The only local variable of coef: its argument phi. -/
abbrev Coef.Dest : ℕ := 0

open Coef in
/-- Stores the numbers of the list l, each of them 1, 0 or -1, into the cells from phi + i on. -/
def storeSigns : ℕ → List ℤ → Stmt
  | _, [] => .skip
  | i, x :: l => .store (v Dest +' k i) (signExpr x) ;; storeSigns (i + 1) l

/-- coef(phi). -/
def coefBody : Stmt := storeSigns 0 (Spec.phiFlat ++ Spec.psiFlat)

/-- A coefficient's expression stays within the limits and gives the coefficient. -/
theorem signExpr_gives (h1 : (1 : ℤ) ≤ lim.word) {x : ℤ} (hx : x = 1 ∨ x = 0 ∨ x = -1)
    (σ : State) : (signExpr x).Gives lim σ x := by
  rcases hx with rfl | rfl | rfl <;> simp [signExpr] <;> omega

/-- A coefficient's expression costs at most 3 steps. -/
theorem signExpr_cost (x : ℤ) : (signExpr x).cost ≤ 3 := by
  unfold signExpr
  split_ifs <;> simp

/-- **storeSigns** writes the list to the cells from base + i on, changes nothing else, and takes
at most 7 steps for each number. -/
theorem storeSigns_spec (std : Std lim) {base : ℕ} (l : List ℤ) (i : ℕ) (μ : ℕ → ℤ)
    (hl : ∀ x ∈ l, x = 1 ∨ x = 0 ∨ x = -1) (hsp : base + i + l.length ≤ lim.space) :
    Ends lim P d (storeSigns i l) ⟨frame [base], μ⟩ (7 * l.length) fun σ' =>
      Seg σ'.mem (base + i) l ∧ SameOutside μ σ'.mem (base + i) l.length := by
  light_facts std
  induction l generalizing i μ with
  | nil => exact Ends.skip ⟨Seg.nil, .refl⟩
  | cons x l ih =>
    rw [List.length_cons] at hsp ⊢
    have := signExpr_cost x
    -- mem[phi + i] := x, in at most 7 steps, and then the rest of the list
    refine Ends.storeToThen (base + i) x
      ((ih (i + 1) _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (by omega)).mono
        (by simp; omega) ?_)
      (he := ⟨by light_side, signExpr_gives (by omega) (hl x List.mem_cons_self) _, by omega⟩)
      (hT := by simp; omega)
    rintro σ' ⟨hrest, same⟩
    refine ⟨seg_cons.2 ⟨?_, by rwa [Nat.add_assoc]⟩, fun b hb => ?_⟩
    · rw [same (base + i) (Or.inl (by omega)), Function.update_self]
    · rw [same b (by omega), Function.update_of_ne (by omega)]

/-- All coefficients are 1, 0 or -1. -/
theorem coef_signs :
    ∀ x ∈ Spec.phiFlat ++ Spec.psiFlat, x = 1 ∨ x = 0 ∨ x = -1 := by
  simp [Spec.phiFlat, Spec.psiFlat, Spec.phiTable, Spec.psiTable]

/-- **coef** writes the two tables and changes nothing else, in 7 · 140 steps: the specification
that its callers assume. -/
theorem coef_entry (std : Std lim) (hP : P[pCoef]? = some coefBody) {c : ℕ} (hc : 980 ≤ c) :
    CoefSpec lim P c := by
  intro phi μ hsp d _
  have hlen : (Spec.phiFlat ++ Spec.psiFlat).length = 140 := by simp
  have hphi := Spec.length_phiFlat
  refine ⟨coefBody, hP, (storeSigns_spec std _ 0 μ coef_signs (by omega)).mono (by omega) ?_⟩
  rintro σ' ⟨hcells, same⟩
  rw [Nat.add_zero] at hcells same
  obtain ⟨hphiCells, hpsiCells⟩ := seg_append.1 hcells
  exact ⟨hphiCells, hphi ▸ hpsiCells, hlen ▸ same⟩



open ThreeSumApsp.WordRam

def program5 : Program :=
  [.skip, .skip, powBody, binomBody, sqrtBody, Subsets.subsetTableBody, countersBody,
   digitsBody, coefBody, bandArrayBody, encStepBody, .skip, .skip,
   .skip, .skip, .skip, .skip, .skip, .skip, .skip,
   .skip, .skip, fillBody, copyBody, .skip, .skip]

theorem at_prefix {p : ℕ} {body : Stmt} (h : program5[p]? = some body) (R : Program) :
    (program5 ++ R)[p]? = some body :=
  getElem?_append_of_eq_some h R

def cShared5 : ℕ := 2000

theorem sharedCallees_of_prefix (R : Program) (lim : Limits) (std : Std lim) :
    SharedCallees lim (program5 ++ R) cShared5 where
  pow := pow_entry std (at_prefix rfl R) (by decide)
  binom := binom_entry std (at_prefix rfl R) (by decide)
  sqrt := sqrt_entry (at_prefix rfl R) (by decide)
  coef := coef_entry std (at_prefix rfl R) (by decide)
  subsets := subsets_entry std (at_prefix rfl R) (by decide)
  counters := counters_entry std (at_prefix rfl R) (by decide)
  digits := digits_entry std (at_prefix rfl R) (by decide)




def programThin : Program := program5 ++ [.skip, thinBruteBody, .skip]

end Light.Sec2




/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# What outDigits writes is the output string of the position

Nothing here is about programs.  The digits of the output string of a position are those that
outDigits writes (`digitsO_outStrOfPos`): both lists are the `L` digits of the code of the string
(`digitList_ofDigitList`, `digitList_outCodeOfPos`).
-/


open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The digits of the output string of a position -/

/-- The digits of the output string of the position (I, J), for the computable layout. -/
theorem digitsO_outStrOfPos {L m : ℕ} (hmL : m ≤ L) (I J : ℕ) :
    digitsO (outStrOfPos (stdLayout hmL) I J) = outDigitsOfPos L m I J := by
  have hdigits := digitList_ofDigitList _ (digitsO_lt (outStrOfPos (stdLayout hmL) I J))
  rw [length_digitsO, ofDigitList_digitsO, codeO_outStrOfPos, digitList_outCodeOfPos] at hdigits
  exact hdigits.symm



/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# A query, from the block that holds the data structure (proof of Theorem 30, "Query")

"Given (I, J), we find its tile from the bands of row I and column J, the subset Q of its block
product, and its output string w […], all in O(L) operations". Below, the output string is called η.
queryAt(I, J, b0) has four parts. It reads the sizes, the addresses of the tables and the bands of I
and J from the block at b0 (queryAtReads), computes the addresses of the areas of Section 4
(queryAtAreas), lets outDigits write the digits of η (queryAtOut), reads the root of the trie of the
tile from the table of roots, and lets queryCore compute the sum of Lemma 28 from the two encodings
and this trie (queryAtCore). There is one lemma for each part; for each of the two calls a record
holds the arguments (outArgs, coreArgs) and a lemma says that the block holds what the routine
assumes (outArgs_pre, coreArgs_pre). queryAt_spec puts the four parts together.
-/





/-! ## The program -/

namespace QueryAt

/-- The local variables of queryAt: the arguments I, J, b0; the sizes L, m, t, L - m, K₀, nB, 10^L;
the addresses of the tables BAND, BLOCK, DIG3 and of the area WD; the bands of I and J; the
addresses of the areas BOX, SS, ROOTS, TR; and a local for the result of outDigits, which is not
used. -/
abbrev Row : ℕ := 0
@[inherit_doc Row] abbrev Col : ℕ := 1
@[inherit_doc Row] abbrev Base : ℕ := 2
@[inherit_doc Row] abbrev Levels : ℕ := 3
@[inherit_doc Row] abbrev Inner : ℕ := 4
@[inherit_doc Row] abbrev Switch : ℕ := 5
@[inherit_doc Row] abbrev Outer : ℕ := 6
@[inherit_doc Row] abbrev Blocks : ℕ := 7
@[inherit_doc Row] abbrev Bands : ℕ := 8
@[inherit_doc Row] abbrev Leaves : ℕ := 9
@[inherit_doc Row] abbrev BandTab : ℕ := 10
@[inherit_doc Row] abbrev BlockTab : ℕ := 11
@[inherit_doc Row] abbrev DigitTab : ℕ := 12
@[inherit_doc Row] abbrev Digits : ℕ := 13
@[inherit_doc Row] abbrev BandI : ℕ := 14
@[inherit_doc Row] abbrev BandJ : ℕ := 15
@[inherit_doc Row] abbrev Box : ℕ := 16
@[inherit_doc Row] abbrev Str : ℕ := 17
@[inherit_doc Row] abbrev Roots : ℕ := 18
@[inherit_doc Row] abbrev Tries : ℕ := 19
@[inherit_doc Row] abbrev Void : ℕ := 20

end QueryAt

open QueryAt in
/-- The first part of queryAt(I, J, b0): what is read from the directory and from the table BAND. -/
def queryAtReads : Stmt :=
  .set Levels (M (v Base +' k Dir.levels)) ;;
  .set Inner (M (v Base +' k Dir.inner)) ;;
  .set Switch (M (v Base +' k Dir.switch)) ;;
  .set Outer (M (v Base +' k Dir.outer)) ;;
  .set Blocks (M (v Base +' k Dir.blocks)) ;;
  .set Bands (M (v Base +' k Dir.bands)) ;;
  .set Leaves (M (v Base +' k Dir.leaves)) ;;
  .set BandTab (M (v Base +' k Dir.band)) ;;
  .set BlockTab (M (v Base +' k Dir.block)) ;;
  .set DigitTab (M (v Base +' k Dir.digits)) ;;
  .set Digits (M (v Base +' k Dir.sharedEnd)) ;;
  .set BandI (M (v BandTab +' v Row)) ;;
  .set BandJ (M (v BandTab +' v Col))

open QueryAt in
/-- The second part: the areas of Section 4 lie one behind the other from WD on. -/
def queryAtAreas : Stmt :=
  .set Box (v Digits +' v Levels +' v Levels) ;;
  .set Str (v Box +' v Levels) ;;
  .set Roots (v Str +' v Inner +' k 1) ;;
  .set Tries (v Roots +' v Bands *' v Bands)

open QueryAt in
/-- The call of outDigits: the digits of the output string. -/
def queryAtOut : Stmt :=
  .call Proc.outDigits [M (v BlockTab +' v Row), M (v BlockTab +' v Col),
    v DigitTab +' v Row *' v Outer, v DigitTab +' v Col *' v Outer, M (v Base +' k Dir.mask),
    v Blocks, v Levels, v Digits] Void

open QueryAt in
/-- The call of queryCore: the sum of Lemma 28. The tile of (I, J) has the number bandI nB + bandJ,
and the root of its trie is read from the table of roots. -/
def queryAtCore : Stmt :=
  .call Proc.queryCore [M (v Base +' k Dir.encA) +' v BandI *' v Leaves,
    M (v Base +' k Dir.encB) +' v BandJ *' v Leaves, v Tries,
    M (v Roots +' (v BandI *' v Bands +' v BandJ)), v Digits, v Str, v Box, v Levels, v Inner,
    v Switch] Row

/-- queryAt(I, J, b0) returns (XY)[I, J]: the result of a procedure is its local 0, into which the
last call stores. -/
def queryAtBody : Stmt := queryAtReads ;; queryAtAreas ;; queryAtOut ;; queryAtCore

/-- What the locals hold after the first part. -/
def queryAtRead (p : Sec2.Par) (t b0 I J : ℕ) : List ℤ :=
  [I, J, b0, p.L, p.m, t, p.Lo, p.K0, p.nB, p.T, p.aBAND b0, p.aBLOCK b0, p.aDIG3 b0, aWD p b0,
    (I / (p.K0 * p.N0) : ℕ), (J / (p.K0 * p.N0) : ℕ)]

/-- What the locals hold after the second part. -/
def queryAtLocals (p : Sec2.Par) (t b0 I J : ℕ) : List ℤ :=
  queryAtRead p t b0 I J ++ [(aBOX p b0 : ℤ), aSS p b0, aROOTS p b0, aTR p b0]

section Proof

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

/-! ## The first two parts -/

/-- The second part computes the addresses of the areas of Section 4. -/
theorem queryAtAreas_spec (hlim : Lim30 lim p t b0 U) (I J : ℕ) :
    Ends lim P d queryAtAreas ⟨frame (queryAtRead p t b0 I J), μ⟩ 50
      (· = ⟨frame (queryAtLocals p t b0 I J), μ⟩) := by
  light_facts hlim hlim.std
  obtain ⟨⟩ := areas p t b0
  unfold queryAtLocals queryAtRead
  -- the product nB², in the integers
  have htr : ((aROOTS p b0 + p.nB * p.nB : ℕ) : ℤ) = aTR p b0 := by
    exact_mod_cast (by omega : aROOTS p b0 + p.nB * p.nB = aTR p b0)
  have : (0 : ℤ) ≤ (p.nB : ℤ) * p.nB := by positivity
  push_cast at htr
  -- box := digits + L + L; str := box + L; roots := str + m + 1
  light_set (aBOX p b0 : ℕ)
  light_set (aSS p b0 : ℕ)
  light_set (aROOTS p b0 : ℕ)
  -- tries := roots + nB nB
  light_set (aTR p b0 : ℕ)
  rfl

/-! ## The call of outDigits -/

/-- Bits as natural numbers. -/
theorem segN_of_segB {μ : ℕ → ℤ} {a : ℕ} {l : List Bool} (h : Sec2.SegB μ a l) :
    SegN μ a (l.map fun b => if b then 1 else 0) := by
  unfold Sec2.SegB at h
  unfold SegN
  rw [List.map_map]
  convert h using 2
  funext b
  cases b <;> simp

/-- The arguments of the call of outDigits, and the data behind them. -/
def outArgs (p : Sec2.Par) (b0 I J : ℕ) : OutDigitsArgs :=
  ⟨I / p.N0 % p.K0, J / p.N0 % p.K0, p.aDIG3 b0 + I * p.Lo, p.aDIG3 b0 + J * p.Lo, p.aMASK b0, p.K0,
    p.L, aWD p b0, p.m, digitList 3 p.Lo (I % p.N0), digitList 3 p.Lo (J % p.N0)⟩

/-! ## The call of queryCore -/

/-- The number of the tile of the position (I, J). -/
def tileOf (p : Sec2.Par) (I J : ℕ) : ℕ := I / (p.K0 * p.N0) * p.nB + J / (p.K0 * p.N0)

/-- The arguments of the call of queryCore, and the data behind them. -/
def coreArgs (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (I J : ℕ) :
    QueryCoreArgs where
  L := p.L
  m := p.m
  t := t
  encA := encRow p hmL X (I / (p.K0 * p.N0))
  encB := encCol p hmL Y (J / (p.K0 * p.N0))
  η := outStrOfPos (stdLayout hmL) I J
  aA := p.aENCA b0 + I / (p.K0 * p.N0) * p.T
  aB := p.aENCB b0 + J / (p.K0 * p.N0) * p.T
  tr := aTR p b0
  root := (dsTries p t hmL X Y).root (tileOf p I J)
  wd := aWD p b0
  ss := aSS p b0
  box := aBOX p b0
  T := (dsTries p t hmL X Y).cells

/-- Every product of two encoded numbers fits in a word. -/
theorem abs_enc_mul_le (hlim : Lim30 lim p t b0 U) (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (β β' : ℕ) (τ : Leaf p.L) :
    |encRow p hmL X β τ * encCol p hmL Y β' τ| ≤ lim.word := by
  obtain ⟨hrow, hcol⟩ := abs_enc_le hmL X Y U hU hX hY β β'
  rw [abs_mul]
  calc |encRow p hmL X β τ| * |encCol p hmL Y β' τ| ≤ (7 ^ p.L * U) * (7 ^ p.L * U) :=
        mul_le_mul (hrow τ) (hcol τ) (abs_nonneg _) ((abs_nonneg _).trans (hrow τ))
    _ ≤ 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) :=
        le_mul_of_one_le_left (mul_self_nonneg _) (one_le_pow₀ (by norm_num))
    _ ≤ lim.word := hlim.value

section Tile

variable (I J : Fin p.N)

/-- The tile of the position (I, J) is one of the nB² tiles. -/
theorem tileOf_lt (hmL : p.m ≤ p.L) : tileOf p I J < p.nB * p.nB :=
  Nat.mul_add_lt_mul (bandOf_lt_numBands hmL p.N I I.isLt) (bandOf_lt_numBands hmL p.N J J.isLt)

/-- It is given by the encodings of the band of I and of the band of J. -/
theorem getElem?_tileOf :
    (tileList p.nB (encRow p hmL X) (encCol p hmL Y))[tileOf p I J]?
      = some ⟨arrT (coreArgs p t hmL b0 X Y I J).encA, arrT (coreArgs p t hmL b0 X Y I J).encB⟩ :=
  getElem?_tileList p.nB _ _ (bandOf_lt_numBands hmL p.N I I.isLt)
    (bandOf_lt_numBands hmL p.N J J.isLt)

variable (ht : t ≤ p.m)

include ht

/-- Every box of the query is found in the trie of the tile. -/
theorem coreArgs_walk (l : List ℕ)
    (hl : l ∈ boxesOf p.m t (digitsO (coreArgs p t hmL b0 X Y I J).η)) :
    WalkOK (coreArgs p t hmL b0 X Y I J).T (coreArgs p t hmL b0 X Y I J).root l :=
  walkOK_allTries ht (getElem?_tileOf (t := t) (b0 := b0) I J)
    (card_innerSetO_outStrOfPos (stdLayout hmL) I J) hl

/-- Every partial sum of the query fits in a word. -/
theorem coreArgs_sums (hlim : Lim30 lim p t b0 U) (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (j : ℕ) :
    |((coreArgs p t hmL b0 X Y I J).terms.take j).sum| ≤ lim.word := by
  obtain ⟨hrow, hcol⟩ := abs_enc_le hmL X Y U hU hX hY ((I : ℕ) / (p.K0 * p.N0))
    ((J : ℕ) / (p.K0 * p.N0))
  have hcard := card_innerSetO_outStrOfPos (stdLayout hmL) I J
  have hterms := queryTerms_allTries ht
    (getElem?_tileOf (t := t) (hmL := hmL) (b0 := b0) (X := X) (Y := Y) I J) hcard
  rw [QueryCoreArgs.terms]
  exact (congrArg (fun l => |(l.take j).sum|) hterms).trans_le
    ((abs_query_partial_sum_le hrow hcol ht hcard j).trans hlim.value)

/-- What queryCore returns for the tile of (I, J) is (XY)[I, J], by Theorem 30. -/
theorem coreArgs_value :
    trieQuery p.m t (arrT (coreArgs p t hmL b0 X Y I J).encA)
      (arrT (coreArgs p t hmL b0 X Y I J).encB) (coreArgs p t hmL b0 X Y I J).T
      (coreArgs p t hmL b0 X Y I J).root (digitsO (coreArgs p t hmL b0 X Y I J).η) = (X * Y) I J :=
  (trieQuery_allTries ht _ _ (getElem?_tileOf I J)
    (card_innerSetO_outStrOfPos (stdLayout hmL) I J)).trans
    (Theorem30.correct t ht (stdLayout hmL) X Y I J)

end Tile

/-! ## The routine -/

end Proof

end Light.Sec4





section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Horner's rule: the code of a string of decimal digits

horner(a, L) returns the number whose L decimal digits, most significant first, are in the cells
from a.  It is used to index an encoding by a leaf (Section 4.3: "The encodings are indexed by the
leaves (Section 2.4.1) […].  Thus reading the product at a leaf […] takes O(L) operations").

After i rounds the routine holds the number formed by the first i digits (`Horner.Inv`).  One more
digit multiplies it by ten and adds the digit (`ofDigitList_take_succ`), and it stays below 10^L
(`ofDigitList_lt`), which fits in a word.  `horner_spec` is the specification.
-/



namespace Light.Sec4

open ThreeSumApsp.Spec

namespace Horner

/-- The local variables of horner: the arguments (the address of the string and its length), the
level, and the number formed so far.  Local 0 also takes the result. -/
abbrev Str : ℕ := 0
@[inherit_doc Str] abbrev Result : ℕ := 0
@[inherit_doc Str] abbrev Len : ℕ := 1
@[inherit_doc Str] abbrev Level : ℕ := 2
@[inherit_doc Str] abbrev Acc : ℕ := 3

/-- Before round i the number formed by the first i digits has been computed.  The memory is not
changed. -/
def Inv (a : ℕ) (l : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [a, l.length, i, (ofDigitList 10 (l.take i) : ℕ)], μ⟩

end Horner

open Horner in
/-- horner(str, len): multiply by ten and add the next digit, from the most significant digit on. -/
def hornerBody : Stmt :=
  .set Level (k 0) ;;
  .set Acc (k 0) ;;
  .while (v Level <' v Len) (
    .set Acc (v Acc *' k 10 +' M (v Str +' v Level)) ;;
    .set Level (v Level +' k 1)) ;;
  .set Result (v Acc)

open Horner in
/-- **horner** returns the number with the given decimal digits, and leaves the memory as it
was. -/
theorem horner_spec {lim : Limits} {P : Program} (hP : P[Proc.horner]? = some hornerBody)
    (hs : Std lim) : HornerSpec lim P := by
  rintro a _ l μ hseg rfl hd ha hpow
  refine fun d _ => ⟨hornerBody, hP, ?_⟩
  light_facts hs
  -- every number formed on the way is below 10^L, so it fits in a word
  have hfits : ∀ i ≤ l.length, ((ofDigitList 10 (l.take i) : ℕ) : ℤ) < lim.word := fun i hi => by
    have hlt := ofDigitList_lt (b := 10) (l.take i) fun x hx => hd x (List.mem_of_mem_take hx)
    have hpow' : 10 ^ (l.take i).length ≤ 10 ^ l.length :=
      Nat.pow_le_pow_right (by norm_num) (List.length_take_le' _ _)
    exact lt_of_lt_of_le (by exact_mod_cast hlt.trans_le hpow') hpow
  unfold tHorner
  -- level := 0; acc := 0
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- while level < len
  refine Ends.next _ (Ends.whileBlock (Inv a l μ) l.length ?start ?round ?done (hT := le_rfl))
  case start => rfl
  case round =>
    rintro i _ hi rfl
    have hcell : μ (a + i) = (l.getD i 0 : ℕ) := hseg.read hi
    have hnext : ((ofDigitList 10 (l.take (i + 1)) : ℕ) : ℤ)
        = (ofDigitList 10 (l.take i) : ℕ) * 10 + (l.getD i 0 : ℕ) := by
      exact_mod_cast ofDigitList_take_succ 10 l hi
    have := hfits (i + 1) hi
    generalize l.getD i 0 = digit at hcell hnext
    -- acc := acc * 10 + mem[str + level]; level := level + 1
    refine ⟨by light_side, by light_side, by light_side [hcell], ?_⟩
    simp [Horner.Inv, update_frame_setLocal, hcell, hnext]
  case done =>
    rintro _ rfl
    refine ⟨by light_side, by light_side, ?_⟩
    -- return acc
    light_set (ofDigitList 10 l : ℕ) using List.take_length
    exact ⟨rfl, rfl⟩

end Light.Sec4

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Looking up a string in a trie (Section 4.3)

"looking up or inserting a box, takes O(L) operations": the routine follows the symbols of the box
down from the root.  A vertex is a block of eleven consecutive cells of the trie area, one for each
symbol, holding the address of the child; a vertex at depth L holds the value in its first cell.
Addresses are relative to the base of the area, so the model is `Spec.trieLookup` on the array T
that the area holds.

The loop goes down one level in each round.  Its invariant (`Lookup.Inv`) says that the walk from
the current vertex along the rest of the string ends where the walk from the root along the whole
string ends, and that it stays inside the array (`Spec.WalkOK`); `Lookup.walk_step` says what one
step down does to both facts.  `lookup_spec` is the specification.
-/


namespace Light.Sec4

open ThreeSumApsp.Spec

namespace Lookup

/-- The local variables of lookup: the arguments (the base of the trie area, the root, which becomes
the current vertex, the address of the string and its length) and the level.  Local 0 also takes the
result. -/
abbrev Area : ℕ := 0
@[inherit_doc Area] abbrev Result : ℕ := 0
@[inherit_doc Area] abbrev Vertex : ℕ := 1
@[inherit_doc Area] abbrev Key : ℕ := 2
@[inherit_doc Area] abbrev Len : ℕ := 3
@[inherit_doc Area] abbrev Level : ℕ := 4

end Lookup

open Lookup in
/-- lookup(area, root, key, len): follow the symbols of the string down from the root, and return
the first cell of the vertex that is reached. -/
def lookupBody : Stmt :=
  .set Level (k 0) ;;
  .while (v Level <' v Len) (
    .set Vertex (M (v Area +' v Vertex +' M (v Key +' v Level))) ;;
    .set Level (v Level +' k 1)) ;;
  .set Result (M (v Area +' v Vertex))

namespace Lookup

variable {T : List ℤ} {kl : List ℕ} {p i : ℕ}

/-- One step down: the current vertex lies inside the array, the pointer for the next symbol is
positive, and the walk goes on from the child. -/
theorem walk_step (hi : i < kl.length) (hok : WalkOK T p (kl.drop i)) :
    p + 11 ≤ T.length ∧ 0 < T.getD (p + kl[i]) 0 ∧
      WalkOK T (T.getD (p + kl[i]) 0).toNat (kl.drop (i + 1)) ∧
      trieWalk T p (kl.drop i) = trieWalk T (T.getD (p + kl[i]) 0).toNat (kl.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi] at hok ⊢
  exact ⟨hok.2.1, hok.2.2.1, hok.2.2.2, rfl⟩

/-- Before round i: the walk from the current vertex p along the rest of the string stays inside the
array and ends where the walk from the root ends.  The memory is not changed. -/
def Inv (tr root key : ℕ) (T : List ℤ) (kl : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ p : ℕ, σ = ⟨frame [tr, p, key, kl.length, i], μ⟩ ∧ WalkOK T p (kl.drop i) ∧
    trieWalk T root kl = trieWalk T p (kl.drop i)

end Lookup

open Lookup in
/-- **lookup** returns the value stored for the string, and leaves the memory as it was. -/
theorem lookup_spec {lim : Limits} {P : Program} (hP : P[Proc.lookup]? = some lookupBody)
    (hs : Std lim) : LookupSpec lim P := by
  rintro tr root key _ T kl μ hT hkey rfl hd hwalk htr hkeyB
  refine fun d _ => ⟨lookupBody, hP, ?_⟩
  light_facts hs
  unfold tLookup
  -- level := 0
  light_set (0 : ℕ)
  -- while level < len
  refine Ends.next _ (Ends.whileBlock (Inv tr root key T kl μ) kl.length ?start ?round ?done
    (hT := le_rfl))
  case start => exact ⟨root, rfl, hwalk, rfl⟩
  case round =>
    rintro i _ hi ⟨p, rfl, hok, hwk⟩
    obtain ⟨hpT, hpos, hok', hstep⟩ := walk_step hi hok
    have : kl[i] < 11 := hd _ (List.getElem_mem hi)
    have hcell : μ (key + i) = (kl[i] : ℕ) := hkey.getElem hi
    have hnext : μ (tr + (p + kl[i])) = T.getD (p + kl[i]) 0 := hT.getD (by omega) 0
    have haddr : ((tr : ℤ) + p + (kl[i] : ℕ)).toNat = tr + (p + kl[i]) := by omega
    -- vertex := mem[area + vertex + mem[key + level]]; level := level + 1
    refine ⟨by light_side, by light_side, by light_side [hcell],
      (T.getD (p + kl[i]) 0).toNat, ?_, hok', hwk.trans hstep⟩
    rw [Int.toNat_of_nonneg hpos.le]
    simp [update_frame_setLocal, hcell, haddr, hnext]
  case done =>
    rintro _ ⟨p, rfl, hok, hwk⟩
    rw [List.drop_of_length_le le_rfl] at hok hwk
    have := hok.2
    have hread : μ (tr + p) = T.getD p 0 := hT.getD (by omega) 0
    refine ⟨by light_side, by light_side, ?_⟩
    -- return mem[area + vertex]
    light_set (T.getD p 0) using hread
    refine ⟨?_, rfl⟩
    rw [trieLookup, hwk]
    rfl

end Light.Sec4

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The value of a box with stars (proof of Lemma 29, "The values")

"For a box π with e ≥ 1 stars, let ℓ be the highest level at which π has a star.  The leaves of π
are the leaves of the ten strings π[ℓ ← λ] obtained by replacing that star by a term λ, and each of
these strings is again a box, with e - 1 stars. […] Hence we compute val(π) = ∑_λ val(π[ℓ ← λ]) with
ten lookups in the trie, in O(L) operations."  The routine writes the ten digits one after the other
at the position of the star, looks each string up, adds, and puts the star back.  It looks in the
trie of the tile, which is being filled.

Before round j the sum of the first j values has been formed, and the memory differs from the
original one at the position of the star only (`SumTen.Inv`).  `SumTenPre` collects what the
routine assumes.  In a round the string with the digit j at the position of the star stands in the
memory (`segN_set`), so lookup returns its value (`SumTen.round_spec`); `sumTen_spec` is the
specification.
-/


namespace Light.Sec4

open ThreeSumApsp.Spec

namespace SumTen

/-- The local variables of sumTen: the arguments (the base of the trie area, the root of the trie,
the address of the box, its length, the position of the star), the digit that stood at that
position, the digit written, the sum, and a value looked up.  Local 0 also takes the result. -/
abbrev Area : ℕ := 0
@[inherit_doc Area] abbrev Result : ℕ := 0
@[inherit_doc Area] abbrev Root : ℕ := 1
@[inherit_doc Area] abbrev Box : ℕ := 2
@[inherit_doc Area] abbrev Len : ℕ := 3
@[inherit_doc Area] abbrev Star : ℕ := 4
@[inherit_doc Area] abbrev Saved : ℕ := 5
@[inherit_doc Area] abbrev Digit : ℕ := 6
@[inherit_doc Area] abbrev Sum : ℕ := 7
@[inherit_doc Area] abbrev Val : ℕ := 8

end SumTen

open SumTen in
/-- One round: write the digit at the position of the star, look the string up, and add. -/
def sumTenRound : Stmt :=
  .store (v Box +' v Star) (v Digit) ;;
  .call Proc.lookup [v Area, v Root, v Box, v Len] Val ;;
  .set Sum (v Sum +' v Val)

open SumTen in
/-- sumTen(area, root, box, len, star): the sum of the values of the ten strings; the digit at the
position of the star is put back at the end. -/
def sumTenBody : Stmt :=
  .set Saved (M (v Box +' v Star)) ;;
  .set Sum (k 0) ;;
  Stmt.for Digit (k 10) sumTenRound ;;
  .store (v Box +' v Star) (v Saved) ;;
  .set Result (v Sum)

/-- A string with one digit replaced, in the memory. -/
theorem segN_set {μ μ' : ℕ → ℤ} {a p : ℕ} {l : List ℕ} (h : SegN μ a l)
    (hp : p < l.length) (x : ℕ) (hx : μ' (a + p) = x) (ho : ∀ b, b ≠ a + p → μ' b = μ b) :
    SegN μ' a (l.set p x) := by
  intro i hi
  have hi' : i < l.length := by simpa using hi
  by_cases hip : i = p
  · subst hip
    simp [hx]
  · rw [ho _ (by omega), SegN.getElem h hi']
    simp [List.getElem_set_of_ne (Ne.symm hip)]

namespace SumTen

/-- Before round j: the sum of the first j of the ten values has been formed, and the memory differs
from μ at the position of the star only. -/
def Inv (x : SumTenArgs) (saved : ℕ) (μ : ℕ → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (val : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.tr, x.root, x.box, x.l.length, x.p, saved, j, (x.values.take j).sum, val], μ'⟩ ∧
      SameOn (· ≠ x.box + x.p) μ μ'

/-- The time of a round. -/
def tRound (L : ℕ) : ℕ := tLookup L + 15

/-- One round adds the value of the string with the digit j.  The conclusion has the form that the
rule for counting loops asks for: the loop itself then raises the digit. -/
theorem round_spec {lim : Limits} {P : Program} {d : ℕ} (hLookup : LookupSpec lim P)
    (hs : Std lim) {x : SumTenArgs} {saved j : ℕ} {val : ℤ} {μ μ' : ℕ → ℤ}
    (C : SumTenPre lim μ x) (hdep : d + 1 ≤ lim.depth) (hj : j < 10)
    (hsame : SameOn (· ≠ x.box + x.p) μ μ') :
    Ends lim P d sumTenRound
      ⟨frame [x.tr, x.root, x.box, x.l.length, x.p, saved, j, (x.values.take j).sum, val], μ'⟩
      (tRound x.l.length) fun σ' => σ'.loc Digit = j ∧
        Inv x saved μ (j + 1) { σ' with loc := Function.update σ'.loc Digit ((j : ℤ) + 1) } := by
  have hp := C.star
  have hboxB := C.box_in
  light_facts C hs
  have hsum := C.sums (j + 1) (by omega)
  unfold tRound
  -- mem[box + star] := digit
  light_store (x.box + x.p) j
  have hsame₁ : SameOn (· ≠ x.box + x.p) μ (Function.update μ' (x.box + x.p) j) :=
    hsame.write (by simp) _
  have hdigits : ∀ d ∈ x.l.set x.p j, d < 11 := fun d hd => by
    rcases List.mem_or_eq_of_mem_set hd with h | h
    · exact C.digits d h
    · omega
  -- val := lookup(area, root, box, len)
  light_call (hLookup x.tr x.root x.box x.l.length x.T (x.l.set x.p j) _
    C.area.keep
    (segN_set C.seg hp j (Function.update_self _ _ _) hsame₁) (by simp) hdigits (C.walk j hj)
    C.area_in hboxB _ (by omega)) with _ _ ⟨rfl, rfl⟩
  have hnext : (x.values.take (j + 1)).sum
      = (x.values.take j).sum + trieLookup x.T x.root (x.l.set x.p j) :=
    List.sum_take_map_range_succ (fun d => trieLookup x.T x.root (x.l.set x.p d)) hj
  rw [hnext] at hsum
  -- sum := sum + val
  exact Ends.setTo _ ⟨by simp, _, _, by rw [update_frame_setLocal, hnext]; rfl, hsame₁⟩
    ⟨by simpa using hsum, rfl⟩

end SumTen

open SumTen in
/-- **sumTen** returns the sum of the values of the ten strings, and leaves the memory as it
was. -/
theorem sumTen_spec {lim : Limits} {P : Program} (hP : P[Proc.sumTen]? = some sumTenBody)
    (hLookup : LookupSpec lim P) (hs : Std lim) : SumTenSpec lim P := by
  intro x μ pre d hdep
  refine .of_body hP ?_
  rw [SumTenArgs.vals, ← pre.len]
  have hp := pre.star
  light_facts hs pre
  have hsaved : μ (x.box + x.p) = (x.l[x.p] : ℕ) := pre.seg.getElem hp
  unfold tSumTen
  -- saved := mem[box + star]; sum := 0
  light_set (x.l[x.p] : ℕ) using hsaved
  light_set (0 : ℕ)
  -- for digit < 10
  refine Ends.next _ (Ends.for (Inv x x.l[x.p] μ) 10 (tRound x.l.length) ?start ?round ?done ?bound
    (hT := le_rfl)) (by simp [tRound]; omega)
  case start => exact ⟨0, μ, by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl, .refl⟩
  case bound =>
    rintro j _ - - ⟨val, μ', rfl, -⟩
    simp
    omega
  case round =>
    rintro j _ hj - ⟨val, μ', rfl, hsame⟩
    exact round_spec hLookup hs pre hdep hj hsame
  case done =>
    rintro _ - ⟨val, μ', rfl, hsame⟩
    simp only [tRound]
    -- mem[box + star] := saved
    light_store (x.box + x.p) (x.l[x.p] : ℕ)
    -- return sum
    refine Ends.setTo _ ⟨by rw [List.take_of_length_le (by simp [tenValues])]; rfl,
      funext fun b => ?_⟩ ⟨by simp, rfl⟩
    dsimp only
    by_cases hb : b = x.box + x.p
    · rw [hb, Function.update_self, hsaved]
    · rw [Function.update_of_ne hb, hsame b hb]

end Light.Sec4

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The digits of the output string of a position

Proof of Theorem 30, "Query": "Given (I, J), we find its tile from the bands of row I and column J,
the subset Q of its block product, and its output string w (whose variables at the levels outside Q
we read off the row and column of (I, J) within the block product), all in O(L) operations". The
routine walks the mask of the subset: it writes the digit 9 at a level of the subset (levelInner),
and otherwise 3 x + y for the next base-3 digits x and y of the offsets of I and J (levelOuter). The
invariant OutDigits.Inv says what has been written before level l; each of the two branches takes it
from l to l + 1 (OutDigits.inner, OutDigits.outer).
-/


namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The program -/

namespace OutDigits

/-- The local variables of outDigits: the arguments gI, gJ, dI, dJ, aMASK, K0, L, wd, then the
address of the mask of the subset, the level, and the number of levels outside the subset so far. -/
abbrev BlockI : ℕ := 0
@[inherit_doc BlockI] abbrev BlockJ : ℕ := 1
@[inherit_doc BlockI] abbrev DigitsI : ℕ := 2
@[inherit_doc BlockI] abbrev DigitsJ : ℕ := 3
@[inherit_doc BlockI] abbrev Masks : ℕ := 4
@[inherit_doc BlockI] abbrev Blocks : ℕ := 5
@[inherit_doc BlockI] abbrev Levels : ℕ := 6
@[inherit_doc BlockI] abbrev Dest : ℕ := 7
@[inherit_doc BlockI] abbrev Mask : ℕ := 8
@[inherit_doc BlockI] abbrev Level : ℕ := 9
@[inherit_doc BlockI] abbrev Outer : ℕ := 10

end OutDigits

open OutDigits in
/-- A level of the subset: wd[level] := 9; level := level + 1. -/
def levelInner : Stmt :=
  .store (v Dest +' v Level) (k 9) ;;
  .set Level (v Level +' k 1)

open OutDigits in
/-- A level outside the subset: wd[level] := 3 dI[outer] + dJ[outer]; outer := outer + 1;
level := level + 1. -/
def levelOuter : Stmt :=
  .store (v Dest +' v Level) (k 3 *' M (v DigitsI +' v Outer) +' M (v DigitsJ +' v Outer)) ;;
  .set Outer (v Outer +' k 1) ;;
  .set Level (v Level +' k 1)

open OutDigits in
/-- The walk along the mask: while level < L, treat the level according to mask[level]. -/
def outDigitsWalk : Stmt :=
  .while (v Level <' v Levels) (.ite (M (v Mask +' v Level) =' k 1) levelInner levelOuter)

open OutDigits in
/-- outDigits(gI, gJ, dI, dJ, aMASK, K0, L, wd) writes the L digits of the output string at wd. -/
def outDigitsBody : Stmt :=
  .set Mask (v Masks +' (v BlockI *' v Blocks +' v BlockJ) *' v Levels) ;;
  .set Level (k 0) ;;
  .set Outer (k 0) ;;
  outDigitsWalk

namespace OutDigits

/-! ## The pure side: the digit at one level -/

variable {lim : Limits} {μ : ℕ → ℤ} {x : OutDigitsArgs} {l : ℕ} {σ : State}

/-- The mask has one entry for each level. -/
theorem length_mask : x.mask.length = x.L := length_unrank ..

/-- The output string has one digit for each level. -/
theorem length_digits : x.digits.length = x.L := length_outDigits.trans length_mask

/-- The digit at a level of the subset. -/
theorem getD_digits_inner (C : OutDigitsPre lim μ x) (hl : l < x.L)
    (hb : x.mask.getD l false = true) : x.digits.getD l 0 = 9 :=
  getD_outDigits_of_true (count_unrank C.index_lt) (length_mask.symm ▸ hl) hb

/-- The digit at a level outside the subset, and the room behind the pointer. -/
theorem getD_digits_outer (C : OutDigitsPre lim μ x) (hl : l < x.L)
    (hb : x.mask.getD l false = false) :
    (x.mask.take l).count false < x.L - x.m ∧
      x.digits.getD l 0 = 3 * x.rI.getD ((x.mask.take l).count false) 0
        + x.rJ.getD ((x.mask.take l).count false) 0 := by
  have hl' : l < x.mask.length := length_mask.symm ▸ hl
  have hcount : x.mask.count false = x.L - x.m := count_false_unrank C.index_lt
  exact ⟨hcount ▸ List.count_take_lt hl' false hb,
    getD_outDigits_of_false (C.lenI.trans hcount.symm) (C.lenJ.trans hcount.symm) hl' hb⟩

/-- The mask of the subset lies inside the table of the K0² masks. -/
theorem base_add_le (C : OutDigitsPre lim μ x) : x.base + x.L < lim.space := by
  have := Nat.mul_add_le_mul (Nat.mul_add_lt_mul C.gI_lt C.gJ_lt) (le_refl x.L)
  have := C.spaceMasks
  unfold OutDigitsArgs.base
  omega

/-! ## The invariant and the two branches -/

/-- The state before level l: the first l digits have been written, and no cell outside wd has
changed. -/
def Inv (μ : ℕ → ℤ) (x : OutDigitsArgs) (l : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ,
    σ = ⟨frame [x.gI, x.gJ, x.dI, x.dJ, x.aMASK, x.k0, x.L, x.wd, x.base, l,
      ((x.mask.take l).count false : ℕ)], μ'⟩ ∧
    SegN μ' x.wd (x.digits.take l) ∧ SameOutside μ μ' x.wd x.L

/-- The cell of the mask that the test of level l reads. -/
theorem read_mask (C : OutDigitsPre lim μ x) {μ' : ℕ → ℤ} (same : SameOutside μ μ' x.wd x.L)
    (hl : l < x.L) : μ' (x.base + l) = if x.mask.getD l false then 1 else 0 := by
  have hlen := length_mask (x := x)
  have := C.apartMask
  rw [same (x.base + l) (by omega), C.segMask.read (by simp [hlen, hl]),
    List.getD_eq_getElem _ _ (by simp [hlen, hl]), List.getElem_map,
    List.getD_eq_getElem _ _ (by omega)]
  split_ifs <;> rfl

/-- wd[level] := 9; level := level + 1. -/
theorem inner (C : OutDigitsPre lim μ x) (h : Inv μ x l σ) (hl : l < x.L)
    (hb : x.mask.getD l false = true) : levelInner.Runs lim σ (Inv μ x (l + 1)) := by
  obtain ⟨μ', rfl, seg, same⟩ := h
  light_facts C C.std
  have hnext := seg.take_succ (length_digits.symm ▸ hl)
  have hcount : (x.mask.take (l + 1)).count false = (x.mask.take l).count false := by
    rw [List.count_take_succ_getD x.mask false (length_mask.symm ▸ hl) false, hb]
    rfl
  rw [getD_digits_inner C hl hb] at hnext
  refine ⟨by light_side [levelInner], _, ?_, hnext,
    same.update ⟨by omega, by omega⟩ _⟩
  simp [levelInner, update_frame_setLocal, hcount]

/-- wd[level] := 3 dI[outer] + dJ[outer]; outer := outer + 1; level := level + 1. -/
theorem outer (C : OutDigitsPre lim μ x) (h : Inv μ x l σ) (hl : l < x.L)
    (hb : x.mask.getD l false = false) : levelOuter.Runs lim σ (Inv μ x (l + 1)) := by
  obtain ⟨μ', rfl, seg, same⟩ := h
  light_facts C C.std
  obtain ⟨hlt, hdigit⟩ := getD_digits_outer C hl hb
  -- the two digits that the level reads
  have hreadI : μ' (x.dI + (x.mask.take l).count false)
      = ((x.rI.getD ((x.mask.take l).count false) 0 : ℕ) : ℤ) := by
    have := C.apartI
    rw [same _ (by omega)]
    exact C.segI.read (by have := C.lenI; omega)
  have hreadJ : μ' (x.dJ + (x.mask.take l).count false)
      = ((x.rJ.getD ((x.mask.take l).count false) 0 : ℕ) : ℤ) := by
    have := C.apartJ
    rw [same _ (by omega)]
    exact C.segJ.read (by have := C.lenJ; omega)
  have hI3 : x.rI.getD ((x.mask.take l).count false) 0 < 3 :=
    List.getD_of_forall_mem (by norm_num) C.ltI _
  have hJ3 : x.rJ.getD ((x.mask.take l).count false) 0 < 3 :=
    List.getD_of_forall_mem (by norm_num) C.ltJ _
  have hnext := seg.take_succ (length_digits.symm ▸ hl)
  have hcount : (x.mask.take (l + 1)).count false = (x.mask.take l).count false + 1 := by
    rw [List.count_take_succ_getD x.mask false (length_mask.symm ▸ hl) false, if_pos hb]
  rw [hdigit] at hnext
  generalize x.rI.getD ((x.mask.take l).count false) 0 = a at hreadI hI3 hnext
  generalize x.rJ.getD ((x.mask.take l).count false) 0 = b at hreadJ hJ3 hnext
  refine ⟨by light_side [levelOuter, hreadI, hreadJ], _, ?_, hnext,
    same.update ⟨by omega, by omega⟩ _⟩
  simp [levelOuter, update_frame_setLocal, hcount, hreadI, hreadJ]

/-- The walk along the mask writes the digits of the output string. -/
theorem walk {P : Program} {d : ℕ} (C : OutDigitsPre lim μ x) :
    Ends lim P d outDigitsWalk
      ⟨frame [x.gI, x.gJ, x.dI, x.dJ, x.aMASK, x.k0, x.L, x.wd, x.base, (0 : ℕ), (0 : ℕ)], μ⟩
      (40 * x.L + 4) fun σ' => SegN σ'.mem x.wd x.digits ∧ SameOutside μ σ'.mem x.wd x.L := by
  light_facts C.std
  have := base_add_le C
  refine Ends.whileBlock (Inv μ x) x.L ?start ?round ?done
    (by simp [levelInner, levelOuter]; omega)
  case start => exact ⟨μ, rfl, by simp [SegN, Seg], .refl⟩
  case round =>
    rintro l σ hl hI
    have hinner := inner C hI hl
    have houter := outer C hI hl
    obtain ⟨μ', rfl, -, same⟩ := hI
    have hread := read_mask C same hl
    refine ⟨by simp, by simpa using hl, ?_⟩
    -- if mask[level] = 1
    by_cases hb : x.mask.getD l false = true
    · rw [if_pos hb] at hread
      exact .ite_pos (hinner hb) (by simp [hread]) (by light_side)
    · rw [if_neg hb] at hread
      exact .ite_neg (houter (by simpa using hb)) (by simp [hread])
        (by light_side)
  case done =>
    rintro _ ⟨μ', rfl, seg, same⟩
    rw [List.take_of_length_le length_digits.le] at seg
    exact ⟨by simp, by simp, seg, same⟩

/-- The numbers on the way to the address of the mask fit in a word. -/
theorem index_le (C : OutDigitsPre lim μ x) : x.gI * x.k0 + x.gJ ≤ lim.space := by
  have hidx := C.index_lt
  have hbase := base_add_le C
  unfold OutDigitsArgs.base at hbase
  rcases Nat.eq_zero_or_pos x.L with h0 | hL
  · have hm : x.m = 0 := by have := C.m_le; omega
    rw [h0, hm, Nat.choose_self] at hidx
    omega
  · exact (Nat.le_mul_of_pos_right _ hL).trans (by omega)

end OutDigits

open OutDigits in
/-- **outDigits** meets its specification. -/
theorem outDigits_spec {lim : Limits} {P : Program}
    (hP : P[Proc.outDigits]? = some outDigitsBody) : OutDigitsSpec lim P := by
  intro x μ C
  refine fun d _ => ⟨outDigitsBody, hP, ?_⟩
  have := C.std.space_le
  have := index_le C
  have := base_add_le C
  have hprod : ((x.gI * x.k0 : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : x.gI * x.k0 ≤ lim.space)
  have haddr : ((x.base : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega : x.base ≤ lim.space)
  have : (0 : ℤ) ≤ (x.gI : ℤ) * x.k0 := by positivity
  have : (0 : ℤ) ≤ ((x.gI : ℤ) * x.k0 + x.gJ) * x.L := by positivity
  unfold OutDigitsArgs.base at haddr
  push_cast at hprod haddr
  unfold tOutDigits
  -- mask := aMASK + (gI K0 + gJ) L
  light_set x.base using OutDigitsArgs.base
  -- level := 0; outer := 0; the walk
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  exact (walk C).mono (by simp; omega) fun _ h => h

end Light.Sec4

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# A string put at the levels of the inner set

Proof of Theorem 30: a query forms each leaf or box "from the private leaf".  The output string is
the list of its L digits, and the levels of its inner set are the positions of the digit 9.  The
routine copies this list and replaces its digits 9, from the left, by the digits of a second string
(`Spec.scatter`).  If star = 1, the leading digits 9 of the second string (the levels of F_V,
Section 4.2) are written as stars (`Spec.starRunIf`).

One pass, with a pointer into the second string and a flag that says whether the leading run of
nines is still going on.  `Scatter.scatter_step` says what the first digit of
`scatter w (starRunIf flag s)` is and how the rest looks, in terms of the digit, the flag and the
pointer that the program computes (`outDigit`, `nextRun`, `nextPtr`); `Scatter.round_runs` says
that a round of the program computes them.  The invariant (`Scatter.Inv`) is that the digits written
so far, followed by what is still to be written, are the whole string.
-/


namespace Light.Sec4

open ThreeSumApsp.Spec

namespace Scatter

/-! ## One more digit -/

/-- The digit written at a position where the first string has x and the pointer is at a digit y of
the second string; run = 1 says that the leading run of nines is still going on. -/
def outDigit (x y run : ℕ) : ℕ :=
  if x = 9 then (if y = 9 then (if run = 1 then 10 else 9) else y) else x

/-- The flag after that position: a digit other than 9 of the second string ends the run. -/
def nextRun (x y run : ℕ) : ℕ := if x = 9 ∧ y ≠ 9 then 0 else run

/-- The pointer after that position. -/
def nextPtr (x o : ℕ) : ℕ := if x = 9 then o + 1 else o

/-- The first digit of what is still to be written, and the rest. -/
theorem scatter_step {w s : List ℕ} {i o : ℕ} (run : ℕ) (hi : i < w.length)
    (ho : w.getD i 0 = 9 → o < s.length) :
    scatter (w.drop i) (starRunIf (decide (run = 1)) (s.drop o)) =
      outDigit (w.getD i 0) (s.getD o 0) run :: scatter (w.drop (i + 1))
        (starRunIf (decide (nextRun (w.getD i 0) (s.getD o 0) run = 1))
          (s.drop (nextPtr (w.getD i 0) o))) := by
  rw [List.drop_eq_getElem_cons hi, ← List.getD_eq_getElem w 0 hi]
  generalize w.getD i 0 = x at ho ⊢
  by_cases hx : x = 9
  · rw [List.drop_eq_getElem_cons (ho hx), ← List.getD_eq_getElem s 0 (ho hx), hx]
    generalize s.getD o 0 = y
    by_cases hy : y = 9
    · rw [hy, starRunIf_nine_cons, scatter_nine_cons]
      by_cases hrun : run = 1 <;> simp [outDigit, nextRun, nextPtr, hrun]
    · rw [starRunIf_cons_of_ne hy, scatter_nine_cons]
      simp [outDigit, nextRun, nextPtr, hy]
  · rw [scatter_cons_of_ne hx]
    simp [outDigit, nextRun, nextPtr, hx]

/-- After i positions: the digits written so far, the flag and the pointer. -/
structure Progress (star : Bool) (wl sl : List ℕ) (i run o : ℕ) (done : List ℕ) : Prop where
  length : done.length = i
  /-- The pointer has passed one digit for each nine of the first string. -/
  ptr : o = (wl.take i).count 9
  /-- The digits written, followed by what is still to be written, are the whole string. -/
  rest : done ++ scatter (wl.drop i) (starRunIf (decide (run = 1)) (sl.drop o))
    = scatter wl (starRunIf star sl)

theorem Progress.zero (star : Bool) (wl sl : List ℕ) :
    Progress star wl sl 0 (if star then 1 else 0) 0 [] :=
  ⟨rfl, rfl, by cases star <;> rfl⟩

section

variable {star : Bool} {wl sl done : List ℕ} {i run o : ℕ}

/-- At a nine of the first string the pointer is inside the second string. -/
theorem Progress.ptr_lt (h : Progress star wl sl i run o done) (hi : i < wl.length)
    (hsl : sl.length = wl.count 9) (h9 : wl.getD i 0 = 9) : o < sl.length := by
  have hle : (wl.take (i + 1)).count 9 ≤ wl.count 9 := (List.take_sublist _ _).count_le _
  rw [List.count_take_succ_getD wl 9 hi 0, if_pos h9, ← h.ptr] at hle
  omega

/-- One more position: the digit, the flag and the pointer are those that the three functions
give. -/
theorem Progress.succ (h : Progress star wl sl i run o done) (hi : i < wl.length)
    (hsl : sl.length = wl.count 9) :
    Progress star wl sl (i + 1) (nextRun (wl.getD i 0) (sl.getD o 0) run)
      (nextPtr (wl.getD i 0) o) (done ++ [outDigit (wl.getD i 0) (sl.getD o 0) run]) where
  length := by rw [List.length_append, h.length, List.length_singleton]
  ptr := by
    rw [List.count_take_succ_getD wl 9 hi 0, ← h.ptr, nextPtr]
    split_ifs <;> rfl
  rest := by
    rw [List.append_assoc, List.singleton_append, ← scatter_step run hi (h.ptr_lt hi hsl)]
    exact h.rest

end

/-! ## The program -/

/-- The local variables of scatter: the arguments (the addresses of the two strings and of the
copy, the length, and the flag, whose first value is the argument star), the position, the pointer
into the second string, and the digit to be written. -/
abbrev First : ℕ := 0
@[inherit_doc First] abbrev Second : ℕ := 1
@[inherit_doc First] abbrev Dst : ℕ := 2
@[inherit_doc First] abbrev Len : ℕ := 3
@[inherit_doc First] abbrev Run : ℕ := 4
@[inherit_doc First] abbrev Pos : ℕ := 5
@[inherit_doc First] abbrev Ptr : ℕ := 6
@[inherit_doc First] abbrev Digit : ℕ := 7

end Scatter

open Scatter

/-- One round: read a digit of the first string; if it is a nine, take the next digit of the second
string in its place, as a star if it is a nine of the leading run; write the digit, and go on. -/
def scatterRound : Stmt :=
  .set Digit (M (v First +' v Pos)) ;;
  .ite (v Digit =' k 9) (
    .set Digit (M (v Second +' v Ptr)) ;;
    .set Ptr (v Ptr +' k 1) ;;
    .ite (v Digit =' k 9)
      (.ite (v Run =' k 1) (.set Digit (k 10)) .skip)
      (.set Run (k 0)))
    .skip ;;
  .store (v Dst +' v Pos) (v Digit) ;;
  .set Pos (v Pos +' k 1)

/-- scatter(first, second, dst, len, star): copy the first string, with the digits of the second
string in place of its nines.  The locals that are not arguments start at 0. -/
def scatterBody : Stmt := .while (v Pos <' v Len) scatterRound

namespace Scatter

theorem round_cost : scatterRound.blockCost = 37 := rfl

/-- What a round does, for the digit x of the first string and the digit y of the second string at
the pointer. -/
theorem round_runs {lim : Limits} (hs : Std lim) {μ : ℕ → ℤ}
    {w s out L run i o dg x y : ℕ} (hw : w + L < lim.space) (hout : out + L < lim.space)
    (hi : i < L) (hx : μ (w + i) = x) (hy : x = 9 → μ (s + o) = y ∧ s + o + 1 < lim.space) :
    scatterRound.Runs lim ⟨frame [w, s, out, L, run, i, o, dg], μ⟩
      (· = ⟨frame [w, s, out, L, nextRun x y run, (i + 1 : ℕ), nextPtr x o, outDigit x y run],
        Function.update μ (out + i) (outDigit x y run)⟩) := by
  light_facts hs
  have hcastx : ((x : ℤ) = 9) = (x = 9) := by norm_cast
  have hcasty : ((y : ℤ) = 9) = (y = 9) := by norm_cast
  have hcastr : ((run : ℤ) = 1) = (run = 1) := by norm_cast
  have haddr : ((out : ℤ) + i).toNat = out + i := by omega
  simp only [scatterRound, outDigit, nextRun, nextPtr]
  -- The tests of the program: a nine of the first string, a nine of the second, the flag.  In each
  -- case the block is run: the first goal says that every address is in range and every value fits
  -- in a word, the second that the last state is the one stated.
  by_cases h9 : x = 9
  · obtain ⟨hcell, hptr⟩ := hy h9
    by_cases hy9 : y = 9 <;> by_cases hrun : run = 1 <;> constructor <;>
      simp [Limits.Addr, abs_le, update_frame_setLocal, *] <;>
      omega
  · constructor <;> simp [Limits.Addr, abs_le, update_frame_setLocal, *]
    omega

/-- Before round i the first i digits have been written at out. -/
def Inv (w s out : ℕ) (star : Bool) (wl sl : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (run o dg : ℕ) (done : List ℕ),
    σ = ⟨frame [w, s, out, wl.length, run, i, o, dg], μ'⟩ ∧ Progress star wl sl i run o done ∧
      SegN μ' out done ∧ SameOutside μ μ' out wl.length

end Scatter

/-- **scatter** writes `Spec.scatter wl (starRunIf star sl)`. -/
theorem scatter_spec {lim : Limits} {P : Program} (hP : P[Proc.scatter]? = some scatterBody)
    (hs : Std lim) : ScatterSpec lim P := by
  rintro w s out _ star wl sl μ hfirst hsecond rfl hsl hapartW hapartS hw_in hs_in hout_in
  refine fun d _ => ⟨scatterBody, hP, ?_⟩
  unfold tScatter
  -- while pos < len
  refine Ends.whileBlock (Inv w s out star wl sl μ) wl.length ?start ?round ?done
    (by simp [round_cost]; omega)
  case start =>
    refine ⟨μ, _, 0, 0, [], ?_, Progress.zero star wl sl, Seg.nil, .refl⟩
    refine congrArg (State.mk · μ) ((frame_append_zeros _ 3).symm.trans ?_)
    cases star <;> rfl
  case round =>
    rintro i _ hi ⟨μ', run, o, dg, done, rfl, hprog, hdone, hsame⟩
    have hx : μ' (w + i) = (wl.getD i 0 : ℕ) :=
      (hsame _ (by omega)).trans (hfirst.read hi)
    have hy : wl.getD i 0 = 9 → μ' (s + o) = (sl.getD o 0 : ℕ) ∧ s + o + 1 < lim.space :=
      fun h9 => by
        have hptr := hprog.ptr_lt hi hsl h9
        exact ⟨(hsame _ (by omega)).trans (hsecond.read hptr), by omega⟩
    refine ⟨by simp, by simp; omega, (round_runs hs hw_in hout_in hi hx hy).mono fun σ' hσ' =>
      ⟨_, _, _, _, _, hσ', hprog.succ hi hsl, ?_, hsame.update ⟨by omega, by omega⟩ _⟩⟩
    have hsnoc := hdone.snoc (outDigit (wl.getD i 0) (sl.getD o 0) run)
    rwa [hprog.length] at hsnoc
  case done =>
    rintro _ ⟨μ', run, o, dg, done, rfl, hprog, hdone, hsame⟩
    have hall : done = scatter wl (starRunIf star sl) := by
      have hrest := hprog.rest
      rwa [List.drop_length, scatter, List.append_nil] at hrest
    exact ⟨by simp, by simp, hall ▸ hdone, hsame⟩

end Light.Sec4

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The lowest symbols P₀ of a leaf turned into stars

Proof of Lemma 29: "A box in which f of the symbols are P₀ or stars is obtained from a leaf of order
m - f […] by turning the e lowest symbols P₀ of that leaf into stars, for some e ≤ f."  The routine
copies a string of L digits and writes 10 (the star) in place of its first e digits 9
(`Spec.starFirst`).  It returns the position of the last star of the copy, "the highest level at
which π has a star" (proof of Lemma 29), which the dynamic program of Lemma 29 expands
(`Spec.lastStar`).

One pass that keeps two numbers: how many nines have been turned into stars so far, and the
position of the last star so far.  The first section says how one more digit changes the copy and
the two numbers; `StarFirst.round_runs` says that a round of the program does just this;
`StarFirst.Inv` is the invariant of the loop.
-/


namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## One more digit -/

/-- The last star of a list with one more digit. -/
theorem lastStar_concat (l : List ℕ) (x : ℕ) :
    lastStar (l ++ [x]) = if x = 10 then some l.length else lastStar l := by
  induction l with
  | nil => simp [lastStar]
  | cons d l ih =>
    rw [List.cons_append, lastStar, ih, lastStar]
    by_cases hx : x = 10
    · simp [hx]
    · simp only [hx, if_false]

namespace StarFirst

variable {e i : ℕ} {l : List ℕ}

/-- The number of nines among the first i digits that are turned into stars. -/
def turned (e : ℕ) (l : List ℕ) (i : ℕ) : ℕ := min e ((l.take i).count 9)

/-- The position of the last star among the first i digits of the copy (0 if there is none). -/
def lastPos (e : ℕ) (l : List ℕ) (i : ℕ) : ℕ := (lastStar ((starFirst e l).take i)).getD 0

/-- The digit of the copy: a nine becomes a star as long as fewer than e nines have been turned. -/
theorem getD_starFirst_eq (e : ℕ) (l : List ℕ) (i : ℕ) :
    (starFirst e l).getD i 0 = if l.getD i 0 = 9 ∧ turned e l i < e then 10 else l.getD i 0 := by
  rw [getD_starFirst, turned]
  simp

theorem turned_zero : turned e l 0 = 0 := by simp [turned]

/-- One more digit: a nine is turned as long as fewer than e have been. -/
theorem turned_succ (hi : i < l.length) :
    turned e l (i + 1) = if l.getD i 0 = 9 ∧ turned e l i < e then turned e l i + 1
      else turned e l i := by
  rw [turned, turned, List.count_take_succ_getD l 9 hi 0]
  split_ifs <;> omega

/-- One more digit: a star moves the position of the last star. -/
theorem lastPos_succ (hi : i < l.length) :
    lastPos e l (i + 1) = if (starFirst e l).getD i 0 = 10 then i else lastPos e l i := by
  have hi' : i < (starFirst e l).length := by rwa [length_starFirst]
  rw [lastPos, lastPos, List.take_succ_getD _ hi' 0, lastStar_concat, List.length_take,
    Nat.min_eq_left hi'.le]
  split_ifs <;> rfl

/-! ## The program -/

/-- The local variables of starFirst: the arguments (the address of the string, the address of the
copy, the length, the number of stars), the position, the position of the last star so far, the
digit, and the number of nines turned into stars so far.  Local 0 also takes the result. -/
abbrev Src : ℕ := 0
@[inherit_doc Src] abbrev Result : ℕ := 0
@[inherit_doc Src] abbrev Dst : ℕ := 1
@[inherit_doc Src] abbrev Len : ℕ := 2
@[inherit_doc Src] abbrev Stars : ℕ := 3
@[inherit_doc Src] abbrev Pos : ℕ := 4
@[inherit_doc Src] abbrev Last : ℕ := 5
@[inherit_doc Src] abbrev Digit : ℕ := 6
@[inherit_doc Src] abbrev Turned : ℕ := 7

end StarFirst

open StarFirst

/-- One round: read a digit, turn it into a star if it is one of the first e nines, remember the
position if a star is written, write the digit, and go on. -/
def starFirstRound : Stmt :=
  .set Digit (M (v Src +' v Pos)) ;;
  .ite (v Digit =' k 9)
    (.ite (v Turned <' v Stars) (.set Digit (k 10) ;; .set Turned (v Turned +' k 1)) .skip) .skip ;;
  .ite (v Digit =' k 10) (.set Last (v Pos)) .skip ;;
  .store (v Dst +' v Pos) (v Digit) ;;
  .set Pos (v Pos +' k 1)

/-- starFirst(src, dst, len, stars): copy the string, with its first nines as stars, and return the
position of the last star.  The locals that are not arguments start at 0. -/
def starFirstBody : Stmt :=
  .while (v Pos <' v Len) starFirstRound ;;
  .set Result (v Last)

namespace StarFirst

theorem round_cost : starFirstRound.blockCost = 34 := rfl

/-- What a round does, for the digit x that is read, with c nines turned and the last star at p. -/
theorem round_runs {lim : Limits} (hs : Std lim) {μ : ℕ → ℤ} {cur box L e i p x dg c : ℕ}
    (hcur : cur + L < lim.space) (hbox : box + L < lim.space) (hi : i < L) (hc : c ≤ i)
    (hcell : μ (cur + i) = x) :
    starFirstRound.Runs lim ⟨frame [cur, box, L, e, i, p, dg, c], μ⟩
      (· = ⟨frame [cur, box, L, e, (i + 1 : ℕ),
          ((if (if x = 9 ∧ c < e then 10 else x) = 10 then i else p : ℕ) : ℤ),
          ((if x = 9 ∧ c < e then 10 else x : ℕ) : ℤ),
          ((if x = 9 ∧ c < e then c + 1 else c : ℕ) : ℤ)],
        Function.update μ (box + i) ((if x = 9 ∧ c < e then 10 else x : ℕ) : ℤ)⟩) := by
  light_facts hs
  have hcast9 : ((x : ℤ) = 9) = (x = 9) := by norm_cast
  have hcast10 : ((x : ℤ) = 10) = (x = 10) := by norm_cast
  have haddr : ((box : ℤ) + i).toNat = box + i := by omega
  simp only [starFirstRound]
  -- The tests of the program: a nine, fewer than e turned, a star.  In each case the block is run:
  -- the first goal says that every address is in range and every value fits in a word, the second
  -- that the last state is the one stated.
  by_cases h9 : x = 9 <;> by_cases hlt : c < e <;> by_cases h10 : x = 10 <;> constructor <;>
    simp [Limits.Addr, abs_le, update_frame_setLocal, *] <;>
    omega

/-- Before round i the first i digits of the copy have been written, and the two counters are up to
date. -/
def Inv (cur box e : ℕ) (l : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (dg : ℕ),
    σ = ⟨frame [cur, box, l.length, e, i, lastPos e l i, dg, turned e l i], μ'⟩ ∧
      SegN μ' box ((starFirst e l).take i) ∧ SameOutside μ μ' box l.length

end StarFirst

/-- **starFirst** writes the copy with the first e nines as stars, and returns the position of its
last star. -/
theorem starFirst_spec {lim : Limits} {P : Program} (hP : P[Proc.starFirst]? = some starFirstBody)
    (hs : Std lim) : StarFirstSpec lim P := by
  rintro cur box _ e l μ hseg rfl hapart hcur hbox
  refine fun d _ => ⟨starFirstBody, hP, ?_⟩
  have hlen : (starFirst e l).length = l.length := length_starFirst e l
  unfold tStarFirst
  -- while pos < len
  refine Ends.next _ (Ends.whileBlock (Inv cur box e l μ) l.length ?start ?round ?done
    (hT := le_rfl)) (by simp [round_cost]; omega)
  case start =>
    refine ⟨μ, 0, ?_, Seg.nil, .refl⟩
    rw [turned_zero]
    exact congrArg (State.mk · μ) (frame_append_zeros _ 4).symm
  case round =>
    rintro i _ hi ⟨μ', dg, rfl, hcopy, hsame⟩
    have hcell : μ' (cur + i) = (l.getD i 0 : ℕ) :=
      (hsame _ (by omega)).trans (hseg.read hi)
    have hturned : turned e l i ≤ i :=
      (min_le_right _ _).trans (List.count_le_length.trans (List.length_take_le _ _))
    refine ⟨by simp, by simp; omega,
      (round_runs hs hcur hbox hi hturned hcell).mono fun σ' hσ' => ?_⟩
    rw [← getD_starFirst_eq, ← turned_succ hi, ← lastPos_succ hi] at hσ'
    refine ⟨_, _, hσ', ?_, hsame.update ⟨by omega, by omega⟩ _⟩
    have hsnoc := hcopy.snoc ((starFirst e l).getD i 0)
    rwa [List.length_take, hlen, Nat.min_eq_left hi.le,
      ← List.take_succ_getD _ (hlen ▸ hi) 0] at hsnoc
  case done =>
    rintro _ ⟨μ', dg, rfl, hcopy, hsame⟩
    rw [← hlen, List.take_length] at hcopy
    refine ⟨by simp, by simp, ?_⟩
    simp only [round_cost]
    -- return last
    light_set (lastPos e l l.length)
    refine ⟨hcopy, ?_, hsame⟩
    rw [lastPos, ← hlen, List.take_length]
    rfl

end Light.Sec4

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Inserting a string into a trie (Lemma 29)

"inserting them into the trie also takes O(L) operations per box, and adds at most L vertices per
box."  New vertices are taken from the end of the part of the trie area that is in use, whose length
is kept in the cell fp.  No routine relies on what the free part of the area holds: the eleven cells
of a new vertex are cleared.  Addresses are relative to the base of the area, so the models are
`Spec.trieNew` and `Spec.trieInsert`.

1. `Ends.clearLoop` is the rule for the loop that clears cells.  `TrieMem.new` and `TrieMem.set`
   say what the trie area holds after a new vertex has been cleared and after a cell has been
   written.
2. `newRoot_spec`: a new vertex as a root.
3. `alloc_spec`: a new vertex as a child.  `Insertion.child` is the array after the test for the
   child, and `Insertion.Progress.step` says that the insertion goes on from the child in that
   array.
4. `insert_spec`: the loop goes down one level in each round (`Insertion.Inv`,
   `Insertion.round_spec`).
-/


namespace Light.Sec4

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Clearing cells -/

/-- Writes 0 into the cells from the address in local x up to, and not including, the address in
local y. -/
def clearLoop (x y : ℕ) : Stmt :=
  .while (v x <' v y) (
    .store (v x) (k 0) ;;
    .set x (v x +' k 1))

/-- **The rule for clearLoop.**  The loop clears the n cells from a and changes no local but x. -/
theorem Ends.clearLoop (hs : Std lim) {x y a n T : ℕ} {loc μ : ℕ → ℤ} {Q : State → Prop}
    (hxy : y ≠ x) (hx : loc x = a) (hy : loc y = (a + n : ℕ)) (ha : a + n < lim.space)
    (done : Q ⟨Function.update loc x ((a + n : ℕ) : ℤ), wrote μ a (fun _ => 0) n⟩)
    (hT : n * 11 + 4 ≤ T := by light_time) : Ends lim P d (clearLoop x y) ⟨loc, μ⟩ T Q := by
  light_facts hs
  refine Ends.whileBlock (fun j σ => σ = ⟨Function.update loc x ((a + j : ℕ) : ℤ),
    wrote μ a (fun _ => 0) j⟩) n ?start ?round ?done hT
  case start => rw [wrote_zero, Nat.add_zero, ← hx, Function.update_eq_self]
  case round =>
    rintro j _ hj rfl
    have haddr : ((a : ℤ) + j).toNat = a + j := by omega
    refine ⟨by simp, by simp [hxy, hy]; omega, by light_side, ?_⟩
    rw [← wrote_succ]
    simp [haddr, add_assoc]
  case done =>
    rintro _ rfl
    exact ⟨by simp, by simp [hxy, hy], done⟩

/-- The cells that have been cleared. -/
theorem seg_wrote_zero (μ : ℕ → ℤ) (a n : ℕ) :
    Seg (wrote μ a (fun _ => 0) n) a (List.replicate n 0) := fun i hi => by
  rw [wrote_done (by simpa using hi), List.getElem_replicate]

/-! ## The trie area -/

section

variable {μ μ₁ : ℕ → ℤ} {tr cap fp : ℕ} {T : List ℤ}

/-- The trie area after a new vertex has been cleared behind the part in use and the free pointer
has been moved. -/
theorem TrieMem.new (h : TrieMem μ tr cap fp T) (hcap : T.length + 11 ≤ cap) :
    TrieMem (Function.update (wrote μ (tr + T.length) (fun _ => 0) 11) fp ((T.length + 11 : ℕ) : ℤ))
        tr cap fp (trieNew T) ∧
      SameOutsideTrie μ
        (Function.update (wrote μ (tr + T.length) (fun _ => 0) 11) fp ((T.length + 11 : ℕ) : ℤ))
        tr cap fp := by
  have hfp := h.fp_out
  have hsame : SameOutside μ (wrote μ (tr + T.length) (fun _ => 0) 11) (tr + T.length) 11 :=
    sameOutside_wrote le_rfl
  refine ⟨⟨?_, ?_, ?_, hfp⟩, fun b ⟨hb, hbfp⟩ => ?_⟩
  · refine Seg.update_out (seg_append.2
      ⟨h.seg.keep, seg_wrote_zero _ _ _⟩) ?_ _
    rw [List.length_append, List.length_replicate]
    omega
  · rw [Function.update_self, length_trieNew]
  · rw [length_trieNew]
    exact hcap
  · rw [Function.update_of_ne hbfp]
    exact hsame b (by omega)

/-- Writing into a cell of the part of the trie area that is in use. -/
theorem TrieMem.set (h : TrieMem μ tr cap fp T) {q : ℕ} (hq : q < T.length) (x : ℤ) :
    TrieMem (Function.update μ (tr + q) x) tr cap fp (T.set q x) ∧
      SameOutsideTrie μ (Function.update μ (tr + q) x) tr cap fp := by
  have hfp := h.fp_out
  have hcap := h.le_cap
  refine ⟨⟨h.seg.update_in hq x, ?_, by simpa using hcap, hfp⟩,
    fun b hb => Function.update_of_ne (by omega) _ _⟩
  rw [Function.update_of_ne (by omega), h.free, List.length_set]

end

/-! ## A new root -/

namespace NewRoot

/-- The local variables of newRoot: the arguments (the base of the trie area and the address of the
free pointer), the address of the new vertex, and the two ends of its cells in the memory.  Local 0
also takes the result. -/
abbrev Area : ℕ := 0
@[inherit_doc Area] abbrev Result : ℕ := 0
@[inherit_doc Area] abbrev Free : ℕ := 1
@[inherit_doc Area] abbrev New : ℕ := 2
@[inherit_doc Area] abbrev From : ℕ := 3
@[inherit_doc Area] abbrev Upto : ℕ := 4

end NewRoot

open NewRoot in
/-- newRoot(area, free): take a new vertex from the end of the part in use, clear its cells, move
the free pointer, and return the address of the vertex. -/
def newRootBody : Stmt :=
  .set New (M (v Free)) ;;
  .set From (v Area +' v New) ;;
  .set Upto (v From +' k 11) ;;
  clearLoop From Upto ;;
  .store (v Free) (v New +' k 11) ;;
  .set Result (v New)

/-- **newRoot** appends a new vertex to the array, and returns its address. -/
theorem newRoot_spec (hP : P[Proc.newRoot]? = some newRootBody) (hs : Std lim) :
    NewRootSpec lim P := by
  intro tr cap fp T μ hT hcap htr hfp
  refine fun d _ => ⟨newRootBody, hP, ?_⟩
  have hfree := hT.free
  light_facts hs
  unfold tNewRoot
  -- new := mem[free]; from := area + new; upto := from + 11
  light_set T.length using hfree
  light_set (tr + T.length : ℕ)
  light_set (tr + T.length + 11 : ℕ)
  -- clear the cells of the new vertex
  refine Ends.next _ (Ends.clearLoop hs (a := tr + T.length) (n := 11) (by decide) rfl rfl
    (by omega) ?_ (hT := le_rfl))
  rw [update_frame_setLocal]
  -- mem[free] := new + 11
  light_store fp (T.length + 11 : ℕ)
  -- return new
  light_set T.length
  exact ⟨rfl, hT.new hcap⟩

/-! ## A new child -/

namespace Insertion

/-- The local variables of insert: the arguments (the base of the trie area, the root, which becomes
the current vertex, the address of the string, its length, the value, the address of the free
pointer), the level, the address of the cell with the pointer to the child, and, for a new vertex,
its address and the two ends of its cells in the memory. -/
abbrev Area : ℕ := 0
@[inherit_doc Area] abbrev Vertex : ℕ := 1
@[inherit_doc Area] abbrev Key : ℕ := 2
@[inherit_doc Area] abbrev Len : ℕ := 3
@[inherit_doc Area] abbrev Value : ℕ := 4
@[inherit_doc Area] abbrev Free : ℕ := 5
@[inherit_doc Area] abbrev Level : ℕ := 6
@[inherit_doc Area] abbrev Cell : ℕ := 7
@[inherit_doc Area] abbrev New : ℕ := 8
@[inherit_doc Area] abbrev From : ℕ := 9
@[inherit_doc Area] abbrev Upto : ℕ := 10

end Insertion

open Insertion

/-- A new vertex as the child in the current cell. -/
def allocStmt : Stmt :=
  .set New (M (v Free)) ;;
  .store (v Cell) (v New) ;;
  .set From (v Area +' v New) ;;
  .set Upto (v From +' k 11) ;;
  clearLoop From Upto ;;
  .store (v Free) (v New +' k 11)

/-- The time of allocStmt. -/
def tAlloc : ℕ := 144

/-- The new vertex becomes the child in the cell q.  Only the last three locals change. -/
theorem alloc_spec (hs : Std lim) {tr cap fp q p key L i : ℕ} {val x₈ x₉ x₁₀ : ℤ}
    {T : List ℤ} {μ : ℕ → ℤ} (hT : TrieMem μ tr cap fp T) (hq : q < T.length)
    (hcap : T.length + 11 ≤ cap)
    (htr : tr + cap < lim.space) (hfp : fp < lim.space) :
    Ends lim P d allocStmt ⟨frame [tr, p, key, L, val, fp, i, (tr + q : ℕ), x₈, x₉, x₁₀], μ⟩
      tAlloc
      fun σ' => ∃ (y₈ y₉ y₁₀ : ℤ) (μ' : ℕ → ℤ),
        σ' = ⟨frame [tr, p, key, L, val, fp, i, (tr + q : ℕ), y₈, y₉, y₁₀], μ'⟩ ∧
          TrieMem μ' tr cap fp (trieNew (T.set q T.length)) ∧ SameOutsideTrie μ μ' tr cap fp := by
  have hfree := hT.free
  light_facts hs
  obtain ⟨hset, hsame⟩ := hT.set hq (T.length : ℤ)
  have hnew := hset.new (by rw [List.length_set]; exact hcap)
  rw [List.length_set] at hnew
  unfold tAlloc
  -- new := mem[free]
  light_set T.length using hfree
  -- mem[cell] := new
  light_store (tr + q) T.length
  -- from := area + new; upto := from + 11
  light_set (tr + T.length : ℕ)
  light_set (tr + T.length + 11 : ℕ)
  -- clear the cells of the new vertex
  refine Ends.next _ (Ends.clearLoop hs (a := tr + T.length) (n := 11) (by decide) rfl rfl
    (by omega) ?_ (hT := le_rfl))
  rw [update_frame_setLocal]
  -- mem[free] := new + 11
  light_store fp (T.length + 11 : ℕ)
  exact ⟨_, _, _, _, rfl, hnew.1, hsame.trans hnew.2⟩

/-! ## Insertion -/

/-- One round: find the cell with the pointer to the child, make a new child if there is none, and
go down to the child. -/
def insertRound : Stmt :=
  .set Cell (v Area +' v Vertex +' M (v Key +' v Level)) ;;
  .ite (M (v Cell) =' k 0) allocStmt .skip ;;
  .set Vertex (M (v Cell))

/-- insert(area, root, key, len, value, free): go down the string, making new children where there
are none, and write the value into the vertex that is reached. -/
def insertBody : Stmt :=
  Stmt.for Level (v Len) insertRound ;;
  .store (v Area +' v Vertex) (v Value)

namespace Insertion

/-- The pointer to a new child, read back from the array. -/
theorem getD_trieNew_set {T : List ℤ} {q : ℕ} (hq : q < T.length) (x : ℤ) :
    (trieNew (T.set q x)).getD q 0 = x := by
  rw [trieNew, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hq),
    List.getElem?_set_self hq]
  rfl

/-- The array after the test for the child in the cell q: a new vertex has been appended if there
was no child. -/
def child (T : List ℤ) (q : ℕ) : List ℤ :=
  if T.getD q 0 = 0 then trieNew (T.set q T.length) else T

/-- After i levels the array is Ti and the current vertex p: what is left is the insertion of the
rest of the string from p. -/
structure Progress (T : List ℤ) (root : ℕ) (kl : List ℕ) (val : ℤ) (i : ℕ) (Ti : List ℤ) (p : ℕ) :
    Prop where
  ok : InsertOK Ti p (kl.drop i)
  eq : trieInsert T root kl val = trieInsert Ti p (kl.drop i) val
  /-- Each level has added at most one vertex. -/
  len : Ti.length ≤ T.length + 11 * i

section

variable {T Ti : List ℤ} {root i p : ℕ} {kl : List ℕ} {val : ℤ}

/-- The current vertex lies inside the array. -/
theorem Progress.inside (h : Progress T root kl val i Ti p) : p + 11 ≤ Ti.length := by
  have hok := h.ok
  generalize kl.drop i = rest at hok
  cases rest with
  | nil => exact hok.2
  | cons x rest => exact hok.2.1

/-- One level down: in the array with the child, the pointer to the child is positive, and the
insertion goes on from the child. -/
theorem Progress.step (h : Progress T root kl val i Ti p) (hi : i < kl.length)
    (hsym : kl[i] < 11) :
    0 < (child Ti (p + kl[i])).getD (p + kl[i]) 0 ∧
      Progress T root kl val (i + 1) (child Ti (p + kl[i]))
        ((child Ti (p + kl[i])).getD (p + kl[i]) 0).toNat := by
  have := h.inside
  have := h.len
  have hok := h.ok
  have heq := h.eq
  rw [List.drop_eq_getElem_cons hi] at hok heq
  rw [trieInsert] at heq
  obtain ⟨hpos, -, hbranch⟩ := hok
  unfold child
  by_cases hz : Ti.getD (p + kl[i]) 0 = 0
  · -- there is no child: a new vertex at the end of the array
    rw [if_pos hz] at hbranch heq ⊢
    rw [getD_trieNew_set (by omega), Int.toNat_natCast]
    exact ⟨by omega, hbranch, heq, by rw [length_trieNew, List.length_set]; omega⟩
  · -- the child exists
    rw [if_neg hz] at hbranch heq ⊢
    exact ⟨hbranch.1, hbranch.2, heq, by omega⟩

end

/-- Before round i: the area holds an array Ti, the current vertex is p, and what is left is as
`Progress` says; outside the trie area nothing has changed. -/
def Inv (x : InsertArgs) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (Ti : List ℤ) (p : ℕ) (x₇ x₈ x₉ x₁₀ : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.tr, p, x.key, x.kl.length, x.val, x.fp, i, x₇, x₈, x₉, x₁₀], μ'⟩ ∧
      Progress x.T x.root x.kl x.val i Ti p ∧ TrieMem μ' x.tr x.cap x.fp Ti ∧
        SameOutsideTrie μ μ' x.tr x.cap x.fp

section

variable {x : InsertArgs} {i p q : ℕ} {x₇ x₈ x₉ x₁₀ : ℤ} {Ti : List ℤ} {μ μ' : ℕ → ℤ}

/-- The time of a round: the cell, the test, a new vertex, and the step down. -/
def tRound : ℕ := tAlloc + 17

/-- The end of a round, once the area holds the array with the child: vertex := mem[cell].  The
conclusion has the form that the rule for counting loops asks for: the loop itself then raises the
level. -/
theorem down_spec (C : InsertPre lim μ x) {t : ℕ} (ht : 3 ≤ t)
    (hq : q < Ti.length) (hchild : 0 < (child Ti q).getD q 0)
    (hnext : Progress x.T x.root x.kl x.val (i + 1) (child Ti q) ((child Ti q).getD q 0).toNat)
    (hmem : TrieMem μ' x.tr x.cap x.fp (child Ti q))
    (hsame : SameOutsideTrie μ μ' x.tr x.cap x.fp) :
    Ends lim P d (.set Vertex (M (v Cell)))
      ⟨frame [x.tr, p, x.key, x.kl.length, x.val, x.fp, i, (x.tr + q : ℕ), x₈, x₉, x₁₀], μ'⟩ t
      fun σ' => σ'.loc Level = i ∧ Inv x μ (i + 1)
        { σ' with loc := Function.update σ'.loc Level ((i : ℤ) + 1) } := by
  light_facts C hmem
  have : q < (child Ti q).length := by
    unfold child
    split_ifs
    · rw [length_trieNew, List.length_set]
      omega
    · exact hq
  have hread := hmem.seg.getD this 0
  generalize (child Ti q).getD q 0 = c at hchild hnext hread
  light_set (c.toNat : ℕ) using hread
  exact ⟨rfl, _, _, _, _, _, _, _, by rw [update_frame_setLocal]; rfl, hnext, hmem, hsame⟩

/-- One round goes down one level, with a new child if there was none. -/
theorem round_spec (hs : Std lim) (C : InsertPre lim μ x) (hi : i < x.kl.length)
    (hprog : Progress x.T x.root x.kl x.val i Ti p) (hmem : TrieMem μ' x.tr x.cap x.fp Ti)
    (hsame : SameOutsideTrie μ μ' x.tr x.cap x.fp) :
    Ends lim P d insertRound
      ⟨frame [x.tr, p, x.key, x.kl.length, x.val, x.fp, i, x₇, x₈, x₉, x₁₀], μ'⟩ tRound
      fun σ' => σ'.loc Level = i ∧ Inv x μ (i + 1)
        { σ' with loc := Function.update σ'.loc Level ((i : ℤ) + 1) } := by
  have := C.room
  have harea := C.area_in
  have := hprog.inside
  light_facts C hmem hprog hs
  have hsym : x.kl[i] < 11 := C.digits _ (List.getElem_mem hi)
  obtain ⟨hchild, hnext⟩ := hprog.step hi hsym
  have hcell : μ' (x.key + i) = (x.kl[i] : ℕ) :=
    (hsame _ ⟨by omega, by omega⟩).trans (C.seg.getElem hi)
  have hq : p + x.kl[i] < Ti.length := by omega
  unfold tRound
  -- cell := area + vertex + mem[key + level]
  light_set (x.tr + (p + x.kl[i]) : ℕ) using hcell
  generalize p + x.kl[i] = q at hchild hnext hq ⊢
  have hptr : μ' (x.tr + q) = Ti.getD q 0 := hmem.seg.getD hq 0
  -- if mem[cell] = 0
  refine Ends.iteThen (fun hz => ?_) (fun hz => ?_) (by light_side)
  · -- there is no child: a new vertex
    have hz' : Ti.getD q 0 = 0 := by
      rw [← hptr]
      simpa using hz
    refine Ends.next _ ((alloc_spec hs hmem hq (by omega) harea C.free_in).mono le_rfl ?_)
    rintro _ ⟨y₈, y₉, y₁₀, μ₂, rfl, hmem₂, hsame₂⟩
    exact down_spec C (by light_time) hq hchild hnext (by rw [child, if_pos hz']; exact hmem₂)
      (hsame.trans hsame₂)
  · -- the child exists
    have : Ti.getD q 0 ≠ 0 := by
      rw [← hptr]
      simpa using hz
    refine Ends.next 0 (Ends.skip ?_)
    exact down_spec C (by light_time) hq hchild hnext (by rw [child, if_neg this]; exact hmem)
      hsame

end

end Insertion

/-- **insert** stores the value for the string: the area then holds `Spec.trieInsert`. -/
theorem insert_spec (hP : P[Proc.insert]? = some insertBody) (hs : Std lim) :
    InsertSpec lim P := by
  intro x μ pre d _
  refine .of_body hP ?_
  rw [InsertArgs.vals, ← pre.len]
  light_facts hs pre
  unfold tInsert
  -- for level < len
  refine Ends.next _ (Ends.for (Inv x μ) x.kl.length tRound ?start ?round
    ?done ?bound (hT := le_rfl)) (by simp [tRound, tAlloc]; omega)
  case start =>
    exact ⟨x.T, x.root, 0, 0, 0, 0, μ, by rw [update_frame_setLocal, ← frame_append_zeros _ 4]; rfl,
      ⟨pre.walk, rfl, by omega⟩, pre.trie, .refl⟩
  case bound =>
    rintro i _ - - ⟨Ti, p, x₇, x₈, x₉, x₁₀, μ', rfl, -⟩
    simp
  case round =>
    rintro i _ hi - ⟨Ti, p, x₇, x₈, x₉, x₁₀, μ', rfl, hprog, hmem, hsame⟩
    exact round_spec hs pre hi hprog hmem hsame
  case done =>
    rintro _ - ⟨Ti, p, x₇, x₈, x₉, x₁₀, μ', rfl, hprog, hmem, hsame⟩
    have := hprog.inside
    have := hmem.le_cap
    obtain ⟨hset, hsame'⟩ := hmem.set (q := p) (by omega) x.val
    have heq := hprog.eq
    rw [List.drop_length, trieInsert] at heq
    simp only [tRound, tAlloc]
    -- mem[area + vertex] := value
    light_store (x.tr + p) x.val
    exact ⟨heq ▸ hset, hsame.trans hsame'⟩

end Light.Sec4

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The routines of Section 4, assembled

The fourteen routines with the numbers 40 to 53, as a list (procs40), and the theorem that every
program that holds them at these numbers (Has40) meets all their specifications (specs40). Each
routine is proved under the specifications of the routines that it calls; here these assumptions are
discharged, in the order in which the routines call each other. For the programs of Theorem 30, its
offline form and Corollary 26, which hold the fourteen routines behind forty others
(has40_of_append), this gives the specifications of the two routines that know the memory map:
preCoreSpec_of and preCoreSpec_all for the preprocessing, queryAtSpec_all for a query.
-/


namespace Light.Sec4

/-- The bodies of the procedures number 40, 41, …, 53. -/
def procs40 : List Stmt :=
  [nineFirstBody, nineNextBody, scatterBody, starFirstBody, hornerBody, lookupBody, insertBody,
    newRootBody, sumTenBody,
    fillListBody, tileBody, allTilesBody, outDigitsBody, queryCoreBody]

/-- The program P holds the routines of Section 4 at their numbers. -/
def Has40 (P : Program) : Prop := ∀ i < 14, P[40 + i]? = procs40[i]?

structure Specs40 (lim : Limits) (P : Program) : Prop where
  nineFirst : NineFirstSpec lim P
  nineNext : NineNextSpec lim P
  scatter : ScatterSpec lim P
  starFirst : StarFirstSpec lim P
  horner : HornerSpec lim P
  lookup : LookupSpec lim P
  insert : InsertSpec lim P
  newRoot : NewRootSpec lim P
  sumTen : SumTenSpec lim P
  outDigits : OutDigitsSpec lim P

theorem specs40 {lim : Limits} {P : Program} (h : Has40 P) (hs : Std lim) : Specs40 lim P := by
  have nineFirst : NineFirstSpec lim P := nineFirst_spec (h 0 (by omega)) hs
  have nineNext : NineNextSpec lim P := nineNext_spec (h 1 (by omega)) hs
  have scatter : ScatterSpec lim P := scatter_spec (h 2 (by omega)) hs
  have starFirst : StarFirstSpec lim P := starFirst_spec (h 3 (by omega)) hs
  have horner : HornerSpec lim P := horner_spec (h 4 (by omega)) hs
  have lookup : LookupSpec lim P := lookup_spec (h 5 (by omega)) hs
  have insert : InsertSpec lim P := insert_spec (h 6 (by omega)) hs
  have newRoot : NewRootSpec lim P := newRoot_spec (h 7 (by omega)) hs
  have sumTen : SumTenSpec lim P := sumTen_spec (h 8 (by omega)) lookup hs
  have outDigits : OutDigitsSpec lim P := outDigits_spec (h 12 (by omega))
  exact ⟨nineFirst, nineNext, scatter, starFirst, horner, lookup, insert, newRoot, sumTen,
    outDigits⟩

/-- A list that has forty procedures, then the routines of Section 4, then anything, holds them at
their numbers. -/
theorem has40_of_append {A B : List Stmt} (hA : A.length = 40) : Has40 (A ++ procs40 ++ B) := by
  intro i hi
  have : procs40.length = 14 := rfl
  rw [List.append_assoc, List.getElem?_append_right (by omega), hA, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by omega)]

end Light.Sec4

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Theorem 30 on the word RAM: the program

`program30` is the list of procedures: those of Section 2 (numbers 0 to 28, of which the
preprocessing uses the shared stage), the routines of Section 4 (40 to 53), preCore, queryAt and the
two procedures of the offline form (54 to 57), and the two main procedures of Theorem 30 (80 and
81); the unused numbers hold the empty statement.

The first 58 procedures (`base58`) are also the beginning of the programs for Corollaries 26, 31
and 32.  So the assumptions of the earlier files are discharged for every program `base58 ++ R` that
begins with them: it meets the specifications of the preprocessing and of a query at a given place
of the memory (`preCore_base58`, `queryAt_base58`).  With `theorem_30_of` and `theorem_30_wanted_of`
this gives Theorem 30 and its offline form without hypotheses (`wordRam_theorem_30`,
`wordRam_theorem_30_wanted`).
-/


namespace Light.Sec4

open ThreeSumApsp.WordRam

/-- The procedures number 0 to 57: Section 2's program for the thin matrix product (0 to 28), eleven
unused numbers, the routines of Section 4, the two routines that know the memory map, and the two
routines of the offline form. -/
def base58 : Program :=
  Sec2.programThin ++ List.replicate 11 .skip ++ procs40 ++
    [.skip, queryAtBody, .skip, .skip]

theorem length_base58 : base58.length = 58 := rfl

/-- A procedure of base58 is a procedure, with the same number, of every program that begins with
base58. -/
theorem at_base58 {p : ℕ} {body : Stmt} (h : base58[p]? = some body) (R : Program) :
    (base58 ++ R)[p]? = some body :=
  getElem?_append_of_eq_some h R

/-- The constant of the shared stage. -/
def cShared30 : ℕ := 12 * Sec2.cShared5 + 600

theorem has40_base58 (R : Program) : Has40 (base58 ++ R) := by
  have h := has40_of_append (A := Sec2.programThin ++ List.replicate 11 .skip)
    (B := [.skip, queryAtBody, .skip, .skip] ++ R) rfl
  rwa [← List.append_assoc] at h

end Light.Sec4

end
