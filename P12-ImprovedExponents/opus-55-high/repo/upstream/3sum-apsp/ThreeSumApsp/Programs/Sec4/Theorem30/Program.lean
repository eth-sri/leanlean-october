/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.Program
import ThreeSumApsp.Programs.Sec4.Theorem30.Layout
import ThreeSumApsp.Programs.Sec4.Theorem30.OfflineLayout
import ThreeSumApsp.Programs.Sec4.Theorem30.Routines

/-!
# Theorem 30 on the word RAM: the program

`program30` is the list of procedures: those of Section 2 (numbers 0 to 28, of which the
preprocessing uses the shared stage), the routines of Section 4 (40 to 53), preCore, queryAt and the
two procedures of the offline form (54 to 57), and the two main procedures of Theorem 30 (80 and
81); the unused numbers hold the empty statement.

The first 58 procedures (`base58`) are also the beginning of the programs for Corollaries 26, 31
and 32.  So the assumptions of the earlier files are discharged for every program `base58 ++ R` that
begins with them: it meets the specifications of the preprocessing and of a query at a given place
of the memory (`preCore_base58`, `queryAt_base58`).  With `theorem_30_of` and `theorem_30_wanted_of`
this gives Theorem 30 and its offline form without hypotheses (`wordRam_theorem_30`,
`wordRam_theorem_30_wanted`).
-/


namespace Light.Sec4


/-- The procedures number 0 to 57: Section 2's program for the thin matrix product (0 to 28), eleven
unused numbers, the routines of Section 4, the two routines that know the memory map, and the two
routines of the offline form. -/
def base58 : Program :=
  Sec2.programThin ++ List.replicate 11 .skip ++ procs40 ++
    [preCoreBody, queryAtBody, wantedCoreBody, wantedMainBody]



/-- The constant of the shared stage. -/
def cShared30 : ℕ := 12 * Sec2.cShared5 + 600

theorem has40_base58 (R : Program) : Has40 (base58 ++ R) := by
  have h := has40_of_append (A := Sec2.programThin ++ List.replicate 11 .skip)
    (B := [preCoreBody, queryAtBody, wantedCoreBody, wantedMainBody] ++ R) rfl
  assumption
