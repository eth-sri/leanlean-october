/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Lib.Copy
import ThreeSumApsp.Lang.Lib.CountSort
import ThreeSumApsp.Util.StablePass

/-!
# One pass of a radix sort on a list of indices

The pass sorts the list of indices at perm stably by a key that is read through the index: countSort
writes the sorted list into the w cells after the list, and copy brings it back.  What countSort
leaves is the result of a stable pass on lists (`exists_stablePass`), and `radixPass_ends` puts the
two calls together.  The pass is used with different expressions for the place of the keys, so these
are parameters.
-/



namespace Light

namespace RadixPass

/- The local variables that the pass uses: w, perm, and a local that takes the results of the two
calls, which are not used. -/
slots Num
slots 5 Perm
slots 7 Unused

/-- The pass: procedure pc is countSort, procedure pp is copy. -/
def _root_.Light.radixPass (pc pp : ℕ) (ekey estride eoff enb ecnt : Expr) : Stmt :=
  .call pc [v Num, v Perm, v Perm +' v Num, ekey, estride, eoff, enb, ecnt] Unused ;;
  .call pp [v Perm +' v Num, v Perm, v Num] Unused


end RadixPass

