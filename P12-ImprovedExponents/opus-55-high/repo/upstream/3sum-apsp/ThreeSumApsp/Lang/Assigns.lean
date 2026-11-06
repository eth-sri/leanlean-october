/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Logic

/-!
# A statement changes only the local variables that it assigns

`s.assigns` lists the local variables that the statement `s` assigns: the targets of its
assignments and the result variables of its calls.  A run of `s` leaves every other local variable
as it was (`Exec.loc_eq_of_notMem_assigns`), so every fact about `s` may be extended by "all other
locals are as before" (`Ends.keeping`).  A lemma about a piece of program text therefore speaks
about the memory and about the locals that the piece assigns, and about no other local.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The local variables that a statement assigns: the targets of its assignments and the result
variables of its calls. -/
@[simp] def Stmt.assigns : Stmt → List ℕ
  | .skip => []
  | .set x _ => [x]
  | .store _ _ => []
  | .seq s t => s.assigns ++ t.assigns
  | .ite _ s t => s.assigns ++ t.assigns
  | .while _ s => s.assigns
  | .call _ _ x => [x]

end Light
