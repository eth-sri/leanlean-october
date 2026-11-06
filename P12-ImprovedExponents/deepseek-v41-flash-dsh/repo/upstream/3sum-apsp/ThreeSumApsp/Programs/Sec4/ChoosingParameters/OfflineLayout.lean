/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Offline
public import ThreeSumApsp.Programs.Sec4.Theorem30.ThinLayout

/-!
# Section 4.4, the offline form: the main procedure for the layout of the statements

The input is N, D, |W|, X, Y, the rows of the wanted positions, their columns (the problem
`thinProduct []`); the output follows the input, and the free pointer follows the output. The text
`offlineMain32Body` serves all rational parameters c and θ: it reads the sizes, computes the
addresses of Y, of the two lists of indices and of the output and the free pointer, and calls
offline32 (`offlineMain32_meets`). The input in the statements of the corollaries
(`ThinInstance.input`) is laid out as the procedure expects (`offlineLayout32_input`). offline32
enters through its specification `OfflineSpec32`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

/-! ## The text -/

namespace OfflineMain32

/-- The locals of offlineMain32: the answer (the two arguments are not used), then N, D, |W|, the
product N D, the addresses of Y, of the rows, of the columns and of the output, the free pointer,
and the result of the call. -/
abbrev Ans : ℕ := 0
@[inherit_doc Ans] abbrev Size : ℕ := 2
@[inherit_doc Ans] abbrev Dim : ℕ := 3
@[inherit_doc Ans] abbrev Count : ℕ := 4
@[inherit_doc Ans] abbrev Area : ℕ := 5
@[inherit_doc Ans] abbrev MatY : ℕ := 6
@[inherit_doc Ans] abbrev Rows : ℕ := 7
@[inherit_doc Ans] abbrev Cols : ℕ := 8
@[inherit_doc Ans] abbrev Out : ℕ := 9
@[inherit_doc Ans] abbrev Free : ℕ := 10
@[inherit_doc Ans] abbrev Res : ℕ := 11

end OfflineMain32

open OfflineMain32 in
/-- offlineMain32: read the sizes, compute the addresses, call offline32, answer 1. -/
def offlineMain32Body : Stmt :=
  .set Size (M (k 0)) ;; .set Dim (M (k 1)) ;; .set Count (M (k 2)) ;;
  .set Area (v Size *' v Dim) ;; .set MatY (k 3 +' v Area) ;; .set Rows (v MatY +' v Area) ;;
  .set Cols (v Rows +' v Count) ;; .set Out (v Cols +' v Count) ;; .set Free (v Out +' v Count) ;;
  .call Proc.offline32 [v Size, v Dim, v Count, k 0, k 3, v MatY, v Rows, v Cols, v Out, v Free]
    Res ;;
  .set Ans (k 1)

/-! ## What it does -/

end Light.Sec4
