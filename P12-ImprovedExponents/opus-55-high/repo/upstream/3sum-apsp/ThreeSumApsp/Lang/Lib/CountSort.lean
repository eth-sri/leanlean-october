/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Lib.Seg
import ThreeSumApsp.Lang.Tactics
import ThreeSumApsp.Util.CountingSort

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



namespace Light

/-! ## The program -/

namespace CountSort

/- The local variables of countSort: the arguments n (Len), src, dst, key (Keys), stride, off
(Offset), nb (Buckets), cnt; the counter of the loops (Idx); the address of a cell of cnt (Cell); a
place in dst (Place). -/
slots Len Src Dst Keys Stride Offset Buckets Cnt Idx Cell Place

end CountSort

open CountSort in
/-- The key of item number i, where i is the value of the counter:
mem[key + src[i] · stride + off]. -/
def csKey : Expr := M (v Keys +' M (v Src +' v Idx) *' v Stride +' v Offset)


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




end CountSort



/-! ## The first phase: the counters are set to 0 -/

/-! ## The second phase: the sizes of the buckets -/

/-! ## The third phase: the starts of the buckets -/

/-! ## The fourth phase: the items go to their places -/

/-! ## The fifth phase: the contents of cnt move up by one cell -/

/-! ## The routine -/

