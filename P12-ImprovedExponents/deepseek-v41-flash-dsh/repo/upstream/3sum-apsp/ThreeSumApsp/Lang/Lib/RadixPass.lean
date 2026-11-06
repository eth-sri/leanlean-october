/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Lang.Lib.CountSort
public import ThreeSumApsp.Util.StablePass

/-!
# One pass of a radix sort on a list of indices

The pass sorts the list of indices at perm stably by a key that is read through the index: countSort
writes the sorted list into the w cells after the list, and copy brings it back.  What countSort
leaves is the result of a stable pass on lists (`exists_stablePass`), and `radixPass_ends` puts the
two calls together.  The pass is used with different expressions for the place of the keys, so these
are parameters.
-/

@[expose] public section

open ThreeSumApsp

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace RadixPass

/-- The local variables that the pass uses: w, perm, and a local that takes the results of the two
calls, which are not used. -/
abbrev Num : ℕ := 0
 abbrev Perm : ℕ := 5
 abbrev Unused : ℕ := 7

/-- The pass: procedure pc is countSort, procedure pp is copy. -/
def _root_.Light.radixPass (pc pp : ℕ) (ekey estride eoff enb ecnt : Expr) : Stmt :=
  .call pc [v Num, v Perm, v Perm +' v Num, ekey, estride, eoff, enb, ecnt] Unused ;;
  .call pp [v Perm +' v Num, v Perm, v Num] Unused

/-- Where the data of a pass lie. -/
structure Args where
  /-- the number of indices -/
  w : ℕ
  /-- where the list of indices stands; the w cells after it are scratch space -/
  perm : ℕ
  /-- the key of the index i is in the cell key + i · stride + off -/
  key : ℕ
  /-- see key -/
  stride : ℕ
  /-- see key -/
  off : ℕ
  /-- all keys are below nb -/
  nb : ℕ
  /-- nb + 1 cells for the counters -/
  cnt : ℕ
  /-- only the R cells from perm on may change -/
  R : ℕ

end RadixPass

variable {μ : ℕ → ℤ} {A : RadixPass.Args} {π : List ℕ} {kd : ℕ → ℕ}

end Light
