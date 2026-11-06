/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Corollary15_16.CountAndDetect
public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters
public import ThreeSumApsp.TimeClaims.Sec3.Arithmetic

/-!
# Corollary 15: splitting the set of query pairs

Corollary 15: "splitting W into sets of at most n²/√D query pairs".  In full:
if #Lop-AE-SparseTri is solved in time T(n, D, w), then it is solved in time
⌈w/s⌉ (T(n, D, s) + O(n D + 1)) + O(w + 1), where s = max(1, ⌊n²/√D⌋) is `splitCap n D`.  This is
`Claim.LopSplit`, with "the problem is solved in time T" read as `LopSolvedIn lopCountTask T`
(`claim_lopSplit`).

The host computes c = max(1, min(⌊n²/√D⌋, w)) and calls the solver on the pieces of c query pairs
(the last piece may be shorter).  A piece is a segment of the arrays of query pairs and of answers,
so nothing is copied, and the two matrices stay where they are.  The number ⌊n²/√D⌋ is the greatest
c with c² D ≤ n⁴; it is found by counting up, and the counting stops at w, because the claim allows
only O(w + 1) steps outside the calls.  If w is smaller than ⌊n²/√D⌋, all query pairs form a single
piece, whether the length of a piece is ⌊n²/√D⌋ as in the claim or min(⌊n²/√D⌋, w) as computed here.

* `lopSplitCount_spec`, `lopSplitCap_spec`: the counting finds c.
* `lopSplitPiece_spec`: one call.  A piece of an instance is an instance (`piece_pre`), and its
  answers are a piece of the answers (`thinOut_piece`).
* `split_spec`: the loop over the pieces.
* `ceilDiv_capW_le`: there are at most as many pieces as in the claim; `polyNeedN_split`: the need
  stays polynomial.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedure -/

namespace LopSplit

/-- The local variables of split beside the ten arguments: the length c of the pieces; N⁴; first the
bound of the counting, then the number lo of query pairs that are done; the length len of the
piece; the result of the call. -/
abbrev C : ℕ := 10
 abbrev N4 : ℕ := 11
 abbrev LO : ℕ := 12
 abbrev LEN : ℕ := 13
 abbrev RES : ℕ := 14

end LopSplit

namespace LopSplitHost

/-! ## Pieces -/

/-! ## The host -/

/-! ## The need stays polynomial -/

end LopSplitHost

end Light.Sec3
