/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Util.CountingSort

/-!
# Counting sort of a list of items by a key that is read through the item

countSort(n, src, dst, key, stride, off, nb, cnt) sorts the n items at src stably by their keys and
writes them to dst.  The key of the item x is the number in the cell key + x · stride + off, a
natural number below nb.  cnt is a scratch area of nb + 1 cells, of arbitrary content on entry; on
exit cnt[t] is the number of items with a key below t, which is where bucket t starts.

The routine has five phases, each of them one loop:
* `csZero` sets the cells of cnt to 0 (`csZero_ends`);
* `csCount` counts the items with key t in cnt[t + 1] (`csCount_ends`);
* `csPrefix` adds up, so that cnt[t] is the start of bucket t (`csPrefix_ends`);
* `csPlace` writes each item to the next free place of its bucket, which it reads from cnt and moves
  on by one (`csPlace_ends`);
* `csShift` moves the contents of cnt up by one cell, so that cnt[t] is again the start of bucket t
  (`csShift_ends`).

Each phase has an invariant, a structure about the memory, with two lemmas: `start` says that it
holds before the first round, and `succ` says what a round does to the memory.  Three numbers
describe the memory, where kf j is the key of item number j: `cntLt kf t n` is the number of items
with a key below t, the start of bucket t; `cntEq kf t i` is the number of items before item number
i with key t; and `sortPos kf n j`, their sum at t = kf j and i = j, is the place of item number j.
What is assumed is `CountSort.Pre`, what is achieved is `CountSort.Post`, and the result is
`countSort_meets`.
-/

@[expose] public section

open ThreeSumApsp

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace CountSort

/-- The local variables of countSort: the arguments n (Len), src, dst, key (Keys), stride, off
(Offset), nb (Buckets), cnt; the counter of the loops (Idx); the address of a cell of cnt (Cell); a
place in dst (Place). -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Dst : ℕ := 2
@[inherit_doc Len] abbrev Keys : ℕ := 3
@[inherit_doc Len] abbrev Stride : ℕ := 4
@[inherit_doc Len] abbrev Offset : ℕ := 5
@[inherit_doc Len] abbrev Buckets : ℕ := 6
@[inherit_doc Len] abbrev Cnt : ℕ := 7
@[inherit_doc Len] abbrev Idx : ℕ := 8
@[inherit_doc Len] abbrev Cell : ℕ := 9
@[inherit_doc Len] abbrev Place : ℕ := 10

end CountSort

open CountSort in
/-- The key of item number i, where i is the value of the counter:
mem[key + src[i] · stride + off]. -/
def csKey : Expr := M (v Keys +' M (v Src +' v Idx) *' v Stride +' v Offset)

@[simp] theorem csKey_cost : csKey.cost = 11 := rfl

open CountSort in
/-- cnt[t] := 0 for t ≤ nb. -/
def csZero : Stmt := .for Idx (v Buckets +' k 1) (.store (v Cnt +' v Idx) (k 0))

open CountSort in
/-- cnt[(key of item i) + 1] += 1 for i < n. -/
def csCount : Stmt :=
  .for Idx (v Len) (.set Cell (v Cnt +' csKey +' k 1) ;; .store (v Cell) (M (v Cell) +' k 1))

open CountSort in
/-- cnt[t + 1] += cnt[t] for t < nb. -/
def csPrefix : Stmt :=
  .for Idx (v Buckets)
    (.store (v Cnt +' v Idx +' k 1) (M (v Cnt +' v Idx +' k 1) +' M (v Cnt +' v Idx)))

open CountSort in
/-- dst[cnt[key of item i]] := item i, cnt[key of item i] += 1, for i < n. -/
def csPlace : Stmt :=
  .for Idx (v Len) (
    .set Cell (v Cnt +' csKey) ;;
    .set Place (M (v Cell)) ;;
    .store (v Dst +' v Place) (M (v Src +' v Idx)) ;;
    .store (v Cell) (v Place +' k 1))

open CountSort in
/-- cnt[t] := cnt[t - 1] for t = nb, …, 1, and cnt[0] := 0. -/
def csShift : Stmt :=
  .set Idx (v Buckets) ;;
  .while (k 0 <' v Idx) (
    .store (v Cnt +' v Idx) (M (v Cnt +' v Idx -' k 1)) ;;
    .set Idx (v Idx -' k 1)) ;;
  .store (v Cnt) (k 0)

/-- countSort(n, src, dst, key, stride, off, nb, cnt). -/
def countSortBody : Stmt := csZero ;; csCount ;; csPrefix ;; csPlace ;; csShift

/-! ## What is assumed, and the state between the phases -/

namespace CountSort

/-- The arguments of countSort. -/
structure Args where
  /-- the number of items -/
  n : ℕ
  /-- where the items stand -/
  src : ℕ
  /-- where the sorted items go -/
  dst : ℕ
  /-- the key of the item x is in the cell key + x · stride + off -/
  key : ℕ
  /-- see key -/
  stride : ℕ
  /-- see key -/
  off : ℕ
  /-- all keys are below nb -/
  nb : ℕ
  /-- nb + 1 cells of scratch space -/
  cnt : ℕ

/-- A state of countSort: the arguments, the counter i, the scratch variables c and p, and the
memory. -/
abbrev Args.state (A : Args) (i c p : ℤ) (μ' : ℕ → ℤ) : State :=
  ⟨frame [A.n, A.src, A.dst, A.key, A.stride, A.off, A.nb, A.cnt, i, c, p], μ'⟩

/-- Only dst and cnt have changed. -/
abbrev Args.Same (A : Args) (μ μ' : ℕ → ℤ) : Prop := SameOutside2 μ μ' A.dst A.n A.cnt (A.nb + 1)

end CountSort

open CountSort

/-- What countSort achieves: item number j stands at dst[sortPos kf n j], cnt[t] is the number of
items with a key below t, and nothing else has changed. -/
structure CountSort.Post (μ : ℕ → ℤ) (A : Args) (it kf : ℕ → ℕ) (μ' : ℕ → ℤ) : Prop where
  placed : ∀ j < A.n, μ' (A.dst + sortPos kf A.n j) = it j
  starts : ∀ t ≤ A.nb, μ' (A.cnt + t) = cntLt kf t A.n
  same : A.Same μ μ'

variable {μ μ' : ℕ → ℤ} {A : Args} {it kf : ℕ → ℕ} {σ : State}

/-- The state between two phases, and before a round of a phase: the counter is i, only dst and cnt
have changed since the start, and R holds of the memory. -/
def CsState (μ : ℕ → ℤ) (A : Args) (i : ℤ) (R : (ℕ → ℤ) → Prop) (σ : State) : Prop :=
  ∃ (c p : ℤ) (μ' : ℕ → ℤ), σ = A.state i c p μ' ∧ A.Same μ μ' ∧ R μ'

/-- A weaker fact about the memory. -/
theorem CsState.imp {entry : ℤ} {R R' : (ℕ → ℤ) → Prop} (h : CsState μ A entry R σ)
    (hR : ∀ μ', R μ' → R' μ') : CsState μ A entry R' σ := by
  obtain ⟨c, p, μ', rfl, same, h⟩ := h
  exact ⟨c, p, μ', rfl, same, hR _ h⟩

/-! ## The first phase: the counters are set to 0 -/

/-! ## The second phase: the sizes of the buckets -/

/-! ## The third phase: the starts of the buckets -/

/-! ## The fourth phase: the items go to their places -/

/-! ## The fifth phase: the contents of cnt move up by one cell -/

/-! ## The routine -/

/-- The time of countSort, for n items and keys below nb. -/
@[simp] def countSortTime (n nb : ℕ) : ℕ := 68 * n + 58 * nb + 52

end Light
