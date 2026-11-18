/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# Theorem 5 in the light language: gathering the codes in sorted order

Section 2.4.4: "sort the sets W_T", the wanted positions of each tile T.  Sorting produces a
permutation of the wanted positions.  The procedure gather(w, perm, src, dst) then copies their
codes into sorted order: dst[i] := src[perm[i]] for i < w.

gather_entry shows that a call ends within 20 (w + 1) steps, with dst[i] = src[π[i]] for the list π
at perm, and that no cell outside the w cells of dst has changed.  The proof is one loop with the
invariant GatherInv; each round reads two cells that are still as at the start and writes dst[i].
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

namespace GatherLocal

/-- The number w of cells. -/
abbrev Len : ℕ := 0
/-- The permutation. -/
abbrev Perm : ℕ := 1
/-- The array that is read. -/
abbrev Src : ℕ := 2
/-- The array that is written. -/
abbrev Dest : ℕ := 3
/-- The counter i of the loop. -/
abbrev Pos : ℕ := 4

end GatherLocal

open GatherLocal

/-- gather(w, perm, src, dst): dst[i] := src[perm[i]] for i < w. -/
def gatherBody : Stmt :=
  .for Pos (v Len) (.store (v Dest +' v Pos) (M (v Src +' M (v Perm +' v Pos))))

end Light.Sec2
