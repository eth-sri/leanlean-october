/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Geometric
public import ThreeSumApsp.Lang.Calls

/-!
# The table of the sizes of Strassen's recursion

szTable(dst, p, J) writes the sizes p, 4p, …, 4^J p of the matrices of Strassen's recursion, the
list `szList p J`, and changes nothing else (`szTable_spec`, `szTable_meets`).
-/

@[expose] public section

namespace Light.Sec3

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The table of the sizes: 4^i p for i ≤ J. -/
def szList (p J : ℕ) : List ℤ := (List.range (J + 1)).map fun i : ℕ => ((4 ^ i * p : ℕ) : ℤ)

/-- The table of the sizes has J + 1 entries. -/
@[simp] theorem length_szList (p J : ℕ) : (szList p J).length = J + 1 := by simp [szList]

/-- szTable(dst, p, J) writes the sizes at each level. -/
def szTableBody : Stmt := geomTable 4

abbrev tSzTable (J : ℕ) := geomTime J

/-- **szTable** as a procedure. -/
theorem szTable_meets {μ : ℕ → ℤ} {q dst p J : ℕ} (hP : P[q]? = some szTableBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (h4 : (4 : ℤ) ≤ lim.word) (hdst : dst + (J + 1) ≤ lim.space)
    (hp : ((4 ^ J * p : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [dst, p, J] μ (tSzTable J) fun _ μ' =>
      Seg μ' dst (szList p J) ∧ SameOutside μ μ' dst (J + 1) :=
  Meets.of_body hP (geomTable_spec (by decide) (fun _ => h4) hw hdst hp)

end Light.Sec3
