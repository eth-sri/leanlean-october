/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# Theorem 5 as a program: the report

Section 2.4.4: "and report, for each (I, J) ∈ W, the value at its output string."

The pruned recursions leave the values in the sorted order of the wanted positions.  report puts
them back in the order in which the positions were given: OUT[PERM[i]] := SV[i].  It is the
counterpart of gather, which reads through the permutation.  `report_entry` is one loop with the
invariant `ReportInv`; the places PERM[i] are different, so no value is overwritten
(`ReportInv.write`).
-/


namespace Light.Sec2


namespace ReportLocal

/- The number w of wanted positions. -/
slots LEN
/- The permutation, sorted order to given order. -/
slots 1 PERM
/- The values, in sorted order. -/
slots 2 VALS
/- The output. -/
slots 3 OUT
/- The place i in the sorted order. -/
slots 4 POS

end ReportLocal

open ReportLocal in
/-- report(w, perm, sv, out): OUT[PERM[i]] := VALS[i] for i < w, where VALS is the array at sv. -/
def reportBody : Stmt :=
  .for POS (v LEN) (.store (v OUT +' M (v PERM +' v POS)) (M (v VALS +' v POS)))

/-! ## The report -/
