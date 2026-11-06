/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec4.Theorem30.Offline

/-!
# Theorem 30, the offline form: the main procedure for the trusted layout

The input is N, D, |W|, m, L, t, X, Y, the rows of the wanted positions, their columns (the problem
thinProduct [m, L, t]); the output follows the input, and the block of the data structure follows
the output.  The main procedure wantedMain reads the sizes, computes the six addresses and calls
wantedCore (`wantedMain_meets`).
-/


namespace Light.Sec4


namespace WantedMain

/- The locals of wantedMain: the answer (the two arguments are not used), then N, D, |W|, the
product N D, the addresses of Y, of the rows, of the columns, of the output and of the block, and
the result of the call. -/
slots Ans
slots 2 Size Dim Count Area MatY Rows Cols Out Block Res

end WantedMain

open WantedMain in
/-- wantedMain: read the sizes, compute the addresses, call wantedCore, answer 1. -/
def wantedMainBody : Stmt :=
  .set Size (M (k 0)) ;; .set Dim (M (k 1)) ;; .set Count (M (k 2)) ;;
  .set Area (v Size *' v Dim) ;; .set MatY (k 6 +' v Area) ;; .set Rows (v MatY +' v Area) ;;
  .set Cols (v Rows +' v Count) ;; .set Out (v Cols +' v Count) ;; .set Block (v Out +' v Count) ;;
  .call Proc.wantedCore [M (k 4), M (k 3), M (k 5), v Size, v Dim, k 6, v MatY, v Rows, v Cols,
    v Count, v Out, v Block] Res ;;
  .set Ans (k 1)
