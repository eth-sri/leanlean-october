/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Logic

/-!
# Two programs in one: relocation of procedures

A program grows by appending procedures.  To put two programs, each with its own numbering of
procedures, into one, the second is placed behind the first (`Program.behind`), and the numbers of
the procedures that it calls are shifted by the length of the first (`Stmt.shift`).

A run of a statement in P is then a run of the shifted statement, with the same states and the
same number of steps (`Exec.shift`, an induction on the run in which only the case of a call has
anything to do: `Program.getElem?_behind_right`).  So everything proved with `Ends` carries over
(`Ends.shift`, `Ends.shift_append`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The statement with n added to the number of every procedure that it calls. -/
def Stmt.shift (n : ℕ) : Stmt → Stmt
  | .skip => .skip
  | .set x e => .set x e
  | .store a e => .store a e
  | .seq s t => .seq (s.shift n) (t.shift n)
  | .ite c s t => .ite c (s.shift n) (t.shift n)
  | .while c s => .while c (s.shift n)
  | .call p args x => .call (p + n) args x

/-- The program P placed behind the program Q. -/
def Program.behind (Q P : Program) := Q ++ P.map (Stmt.shift Q.length)

/-- Procedure p of P is procedure `p + Q.length` of P placed behind Q, with its calls
shifted. -/
theorem Program.getElem?_behind_right Q {p} {body} (h : P[p]? = some body) :
    (Program.behind Q P)[p + Q.length]? = some (body.shift Q.length) := by
  ram_grind [Program.behind]

/-- **Relocation.**  A run in P is a run, with the same states and the same number of steps, of
the shifted statement in P placed behind Q. -/
theorem Exec.shift {s} {σ σ'} {c} (h : Exec lim P d s σ σ' c) Q :
    Exec lim (Program.behind Q P) d (s.shift Q.length) σ σ' c := by
  induction h <;> simp only [Stmt.shift] <;>
    aesop (add unsafe constructors Exec) (add safe apply Program.getElem?_behind_right)

/-- What is proved about a statement in P holds for the shifted statement in P placed behind
Q. -/
theorem Ends.shift {s σ T post} (h : Ends lim P d s σ T post) Q :
    Ends lim (Program.behind Q P) d (s.shift Q.length) σ T post := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.shift Q, hc, hq⟩

/-- The same with more procedures appended behind. -/
def Ends.shift_append {s σ T post} (h : Ends lim P d s σ T post) Q R :=
  (h.shift Q).append R

end Light
