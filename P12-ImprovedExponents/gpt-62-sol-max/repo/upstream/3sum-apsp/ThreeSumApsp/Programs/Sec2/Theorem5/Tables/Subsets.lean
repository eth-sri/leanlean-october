/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.WhileShape
import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Spec.Sec2.Theorem5.SubsetTable

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
`subsetTable_spec` runs through the rows.  `subsets_entry` is
the specification that the callers of the procedure assume.
-/

@[expose] public section

open ThreeSumApsp.Spec.Subsets

namespace Light.Sec2.Subsets

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

/-- The local variables of subsets: Levels = L, Size = m, Rows = KK, Table = mask (the arguments);
Row is the number of the current row and Addr its address; Phase, Ones and Pos are the state of the
scan (phase, number of ones at the end, position found); Cell is the counter of the inner loops. -/
registers [Levels, Size, Rows, Table, Row, Addr, Phase, Ones, Pos, Cell]

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
  refine Ends.iteIffLast (j < m) (fun h => ?_) (fun h => ?_) (by light_side)
  · light_store (a + j) 1
    simp [← wrote_succ, h]
  · light_store (a + j) 0
    simp [← wrote_succ, h]

/-- One round of the scan does to the local variables what `scanStep` says of the cell number j from
the end of the row of L cells that ends just before the address a. -/
theorem scanRound_runs (std : Std lim) (hLa : L ≤ a) (ha : a ≤ lim.space) {j : ℕ} (hj : j < L)
    (hones : 0 ≤ S.ones ∧ S.ones ≤ j) :
    scanRound.Runs lim ⟨frame (locals L m KK mask s a S j), μ⟩ fun σ' => σ' =
      ⟨frame (locals L m KK mask s a (scanStep (μ (a - 1 - j)) ((L : ℤ) - 1 - j) S) j), μ⟩ := by
  light_facts std
  unfold scanRound scanStep
  split <;> rename_i hphase
  · refine .ite_pos ?_
    split <;> rename_i hx
    · exact .ite_pos ⟨by light_side, by simp [update_frame_setLocal]⟩ (by simp_all)
    · exact .ite_neg ⟨by light_side, by simp [update_frame_setLocal]⟩ (by simp_all)
  · refine .ite_neg ?_
    split <;> rename_i hpass
    · refine .ite_pos ?_
      split <;> rename_i hx
      · exact .ite_pos ⟨trivial, rfl⟩ (by simp_all)
      · exact .ite_neg ⟨by light_side, by simp [update_frame_setLocal]⟩ (by simp_all)
    · exact .ite_neg ⟨trivial, rfl⟩

/-- **The scan** of the row of L cells that ends just before the address a changes no cell and
leaves its result in the local variables. -/
theorem scan_spec (std : Std lim) (hLa : L ≤ a) (ha : a ≤ lim.space)
    (done : Q ⟨frame (locals L m KK mask s a (scanAt (prevRow μ a L) L L) L), μ⟩)
    (hT : 33 * L + 12 ≤ T) :
    Ends lim P d scanLoop ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q := by
  light_facts std
  -- Phase := 0; Ones := 0; Pos := 0
  iterate 3 light_step
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
  all_goals (simp_all)

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
  refine Ends.iteIffLast ((j : ℤ) < S.pos) (fun h₁ => ?_) (fun h₁ => ?_)
  · light_store (a + j) (μ (a - L + j)) using haddr, hold
    simp_all
  refine Ends.iteIffLast ((j : ℤ) < S.pos + 1) (fun h₂ => ?_) (fun h₂ => ?_)
  · light_store (a + j) 0
    simp [h₁, h₂]
  refine Ends.iteIffLast ((j : ℤ) < S.pos + 2 + S.ones) (fun h₃ => ?_) (fun h₃ => ?_)
  · light_store (a + j) 1
    simp [h₁, h₂, h₃]
  · light_store (a + j) 0
    simp [h₁, h₂, h₃]

/-- **A further row**: the two passes write the new row to the L cells from a, from the row of L
cells before it, if the result of the scan leaves room. -/
theorem nextRow_spec (std : Std lim) (hLa : L ≤ a) (ha : a + L ≤ lim.space)
    (hroom : (scanAt (prevRow μ a L) L L).Fits L)
    (done : Q ⟨frame (locals L m KK mask s a (scanAt (prevRow μ a L) L L) L),
      wrote μ a (newRow μ a L (scanAt (prevRow μ a L) L L)) L⟩)
    (hT : 64 * L + 18 ≤ T) :
    Ends lim P d nextRow ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q :=
  Ends.next _ (scan_spec std hLa (by omega) (write_spec std hLa ha hroom done (by omega)) le_rfl)

/-- **subsets** writes the table and changes nothing else. -/
theorem subsetTable_spec (std : Std lim) (hmask : mask + KK * L ≤ lim.space) (hm : m ≤ L)
    (hKK : KK ≤ L.choose m) (hKL : ((KK + L : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d subsetTableBody ⟨frame [L, m, KK, mask], μ⟩ (64 * ((KK + 1) * (L + 1))) fun σ' =>
      (∀ s < KK, SegB σ'.mem (mask + s * L) (Spec.unrank L m s)) ∧
        SameOutside μ σ'.mem mask (KK * L) := by
  light_facts std
  push_cast at hKL
  light_steps
  refine Ends.whileShape (fun s (z : Scan × ℤ) ν =>
      ⟨frame (locals L m KK mask s (mask + s * L) z.1 z.2), ν⟩)
    (fun s _ ν => (∀ t < s, SegB ν (mask + t * L) (Spec.unrank L m t)) ∧
      SameOutside μ ν mask (KK * L)) KK (64 * L + 30) (⟨0, 0, 0⟩, 0) μ
    ⟨by simp, .refl⟩ ?_ (fun _ _ h => h)
    (first := by
      simp only [setLocal, Nat.zero_mul, Nat.add_zero]
      rw [← frame_append_zeros _ 4]; rfl)
  rintro s ⟨S, j⟩ ν hs ⟨hrows, same⟩
  have hroom : s * L + L ≤ KK * L := Nat.mul_add_le_mul hs le_rfl
  let a := mask + s * L
  let R (σ : State) := ∃ S' j' η,
    σ = ⟨frame (locals L m KK mask s a S' j'), η⟩ ∧
      SegB η a (Spec.unrank L m s) ∧ SameOutside ν η a L
  have writes (S' : Scan) (f : ℕ → ℤ) (hf : ∀ r < L, f r = bit ((Spec.unrank L m s).getD r false)) :
      R ⟨frame (locals L m KK mask s a S' L), wrote ν a f L⟩ := by
    refine ⟨S', L, _, rfl, fun r hr => ?_, sameOutside_wrote le_rfl⟩
    rw [List.length_map, Spec.length_unrank] at hr
    rw [wrote_done hr, hf r hr, List.getElem_map, List.getD_eq_getElem _ _ (by simp_all)]
    rfl
  unfold tableRow
  refine Ends.pieceThen (T₁ := 64 * L + 22) (R := R) ?_ ?_
  · refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
    · obtain rfl : s = 0 := by simp_all
      exact firstRow_spec std (by simp [a] at *; omega)
        (writes S _ (fun r hr => (bit_unrank_zero hm hr).symm)) (by light_time)
    · obtain ⟨p, rfl⟩ : ∃ p, s = p + 1 := ⟨s - 1, by simp at hc; omega⟩
      have hspace : mask + (p + 1) * L + L ≤ lim.space := by
        have := Nat.mul_add_le_mul hs (le_refl L)
        omega
      have hprev : ∀ q < L, prevRow ν a L q = bit ((Spec.unrank L m p).getD q false) := by
        intro q hq
        rw [prevRow, show a - L + q = mask + p * L + q by simp only [a, Nat.add_mul, Nat.one_mul]; omega]
        exact SegB.get (hrows p (by omega)) (by simp_all)
      have hnext : p + 1 < L.choose m := by omega
      exact nextRow_spec std (by simp only [Nat.add_mul, Nat.one_mul]; omega) hspace (scanAt_fits hnext hprev)
        (writes _ _ (fun r hr => (bit_unrank_succ hnext hprev hr).symm)) (by light_time)
  · rintro _ ⟨S', j', η, rfl, hrow, hkeep⟩
    light_set (s + 1 : ℕ)
    light_set (mask + (s + 1) * L : ℕ) using a, Nat.succ_mul
    refine ⟨(S', j'), η, rfl, fun t ht => ?_, same.trans (hkeep.mono (by omega) (by dsimp [a]; omega))⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
    · have hbefore := Nat.mul_add_le_mul ht (le_refl L)
      exact (hrows t ht).of_sameOutside hkeep (.inl (by rw [List.length_map, Spec.length_unrank]; dsimp [a]; omega))
    · exact hrow

end Light.Sec2.Subsets

namespace Light.Sec2

open Subsets

variable {lim : Limits} {P : Program}

/-- **The specification that the callers of subsets assume.** -/
theorem subsets_entry (std : Std lim) (hP : P[pSubsets]? = some subsetTableBody) {c : ℕ}
    (hc : 64 ≤ c) : SubsetsSpec lim P c :=
  fun _ _ _ _ _ hmask hm hKK hKL _ _ =>
    .mono_const (.of_body hP (subsetTable_spec std hmask hm hKK hKL)) hc

end Light.Sec2
