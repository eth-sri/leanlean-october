/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Instance
public import ThreeSumApsp.Programs.Sec2.Theorem5.Stages
public import ThreeSumApsp.Programs.Sec2.Theorem5.Time

/-!
# Theorem 5: the solver

thm5(N, D, w, U, x, y, wi, wj, out, fr) is the algorithm of Section 2.4.4: find m with D = 4^m; the
shared stage (tables, encodings of all row bands and column bands); the tile, the output string and
its digits for every wanted position; the sort by tile and string; the strings in sorted order; the
pruned recursion on every tile that has a wanted position; the report.  The work area begins at the
free pointer fr.

The result is thm5_spec: on an instance of the thin matrix product in the regime of Theorem 5, the
wanted entries of XY end up in the cells from out on, nothing else below fr changes, and the run
takes at most 2 c + 100 times thm5Shape steps, where c is the constant with which the called
procedures meet their entries.  findM_spec treats the search for m; everything after it is
fromShared_ends, which is stated for arbitrary parameters.  tilesShape_le gives the shape of the
time of the pruned recursions, whatever the sorting permutation, and thm5_time compares the sum of
the times with the shape.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

open ThinArg Solver

/-- The search for m with D = 4^m. -/
def findM : Stmt :=
  .while (v Pow4 <' v Cols) (
    .set Pow4 (v Pow4 *' k 4) ;;
    .set Expo (v Expo +' k 1))

/-- thm5(N, D, w, U, x, y, wi, wj, out, fr): the search for m, then the six stages.  Locals 0 to 9
are the arguments.  Everything that is not in a local is read from the directory, which the shared
stage leaves in the 32 cells from fr on. -/
def thm5Body : Stmt :=
  .set Pow4 (k 1) ;;
  findM ;;
  fromShared

variable {lim : Limits} {P : Program} {c d : ℕ}

end Light.Sec2
