/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.Uniqueness
import Batteries.Tactic.Alias

/-! The statement `DOZZ.IsUpsilon.unique`, proved by `DOZZ.Proofs.IsUpsilon.unique`. -/

public section


namespace DOZZ

/-- Uniqueness of `Υ_{γ/2}` (identity theorem on the strip). -/
alias IsUpsilon.unique := DOZZ.Proofs.IsUpsilon.unique

end DOZZ
