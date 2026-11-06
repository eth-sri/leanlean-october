/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# Theorem 5 as a program: the report

Section 2.4.4: "and report, for each (I, J) ∈ W, the value at its output string."

The pruned recursions leave the values in the sorted order of the wanted positions.  report puts
them back in the order in which the positions were given: OUT[PERM[i]] := SV[i].  It is the
counterpart of gather, which reads through the permutation.  `report_entry` is one loop with the
invariant `ReportInv`; the places PERM[i] are different, so no value is overwritten
(`ReportInv.write`).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

namespace ReportLocal

/-- The number w of wanted positions. -/
abbrev LEN : ℕ := 0
/-- The permutation, sorted order to given order. -/
abbrev PERM : ℕ := 1
/-- The values, in sorted order. -/
abbrev VALS : ℕ := 2
/-- The output. -/
abbrev OUT : ℕ := 3
/-- The place i in the sorted order. -/
abbrev POS : ℕ := 4

end ReportLocal

open ReportLocal
/-- report(w, perm, sv, out): OUT[PERM[i]] := VALS[i] for i < w, where VALS is the array at sv. -/
def reportBody : Stmt :=
  .for POS (v LEN) (.store (v OUT +' M (v PERM +' v POS)) (M (v VALS +' v POS)))

variable {lim : Limits} {P : Program} {c i : ℕ} {μ μ' : ℕ → ℤ}

/-! ## The report -/

end Light.Sec2
