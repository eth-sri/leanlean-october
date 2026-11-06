/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Offline

/-!
# Theorem 30, the offline form: the main procedure for the trusted layout

The input is N, D, |W|, m, L, t, X, Y, the rows of the wanted positions, their columns (the problem
thinProduct [m, L, t]); the output follows the input, and the block of the data structure follows
the output.  The main procedure wantedMain reads the sizes, computes the six addresses and calls
wantedCore (`wantedMain_meets`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp.WordRam

namespace WantedMain

/-- The locals of wantedMain: the answer (the two arguments are not used), then N, D, |W|, the
product N D, the addresses of Y, of the rows, of the columns, of the output and of the block, and
the result of the call. -/
abbrev Ans : ℕ := 0
 abbrev Size : ℕ := 2
 abbrev Dim : ℕ := 3
 abbrev Count : ℕ := 4
 abbrev Area : ℕ := 5
 abbrev MatY : ℕ := 6
 abbrev Rows : ℕ := 7
 abbrev Cols : ℕ := 8
 abbrev Out : ℕ := 9
 abbrev Block : ℕ := 10
 abbrev Res : ℕ := 11

end WantedMain

open WantedMain
/-- wantedMain: read the sizes, compute the addresses, call wantedCore, answer 1. -/
def wantedMainBody : Stmt :=
  .set Size (M (k 0)) ;; .set Dim (M (k 1)) ;; .set Count (M (k 2)) ;;
  .set Area (v Size *' v Dim) ;; .set MatY (k 6 +' v Area) ;; .set Rows (v MatY +' v Area) ;;
  .set Cols (v Rows +' v Count) ;; .set Out (v Cols +' v Count) ;; .set Block (v Out +' v Count) ;;
  .call Proc.wantedCore [M (k 4), M (k 3), M (k 5), v Size, v Dim, k 6, v MatY, v Rows, v Cols,
    v Count, v Out, v Block] Res ;;
  .set Ans (k 1)

end Light.Sec4
