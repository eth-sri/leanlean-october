/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Lang.Compiler.Cells

/-!
# The dispatcher

The machine has no indirect jump.  A return loads the position r to return to into the register RR
and jumps to the dispatcher, the code "RR := RR - 1; if RR < 0 go to j" for j = 0, 1, 2, ….  It
arrives at position r after 2 (r + 1) steps and changes no cell but RR (`steps_dispatcher`).

The proof runs one pair of instructions (`steps_dispatcher_pair`) and then counts down: from the
j-th pair on, with k in RR, the machine arrives at position j + k (`steps_dispatcher_from`).
-/


open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

variable {W : ℕ} {code : List Instr} {disp n : ℕ}

/-- The dispatcher for one more position. -/
theorem dispatcher_succ (n : ℕ) :
    dispatcher (n + 1) = dispatcher n ++ [.sub cRR cRR cONE, .bltz cRR n] := by
  simp [dispatcher, List.range_succ]

/-- Two instructions for each position. -/
theorem length_dispatcher (n : ℕ) : (dispatcher n).length = 2 * n := by
  simp [dispatcher, Nat.mul_comm]

variable {j : ℕ}

/-- A shorter dispatcher is the beginning of a longer one. -/
theorem dispatcher_prefix {n : ℕ} (h : j ≤ n) : dispatcher j <+: dispatcher n := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ n _ ih => grind [dispatcher_succ]

/-- The two instructions for the position j. -/
theorem codeAt_dispatcher (hcode : CodeAt code disp (dispatcher n)) (hj : j < n) :
    CodeAt code (disp + 2 * j) [.sub cRR cRR cONE, .bltz cRR j] := by
  have upToPairCode : CodeAt code disp _ :=
    dispatcher_succ j ▸ (dispatcher_prefix hj).trans hcode
  exact upToPairCode.right.cast_pos (by rw [length_dispatcher])

/-- The two instructions for the position j, when RR holds v: RR goes down by one, and the machine
goes to j if that is negative and to the next pair if not. -/
theorem steps_dispatcher_pair (hcode : CodeAt code disp (dispatcher n))
    (hj : j < n) (m : ℤ → BitVec W) (hone : m cONE = wd W 1) {v : ℤ} (hv : InRange W (v - 1)) :
    Steps code 2 ⟨disp + 2 * j, Function.update m cRR (wd W v)⟩
      ⟨if v - 1 < 0 then j else disp + 2 * (j + 1), Function.update m cRR (wd W (v - 1))⟩ := by
  have pairCode := codeAt_dispatcher hcode hj
  -- RR := RR - 1
  have run₁ := steps_sub pairCode (Function.update_self cRR (wd W v) m)
    
  rw [Function.update_idem] at run₁
  -- if RR < 0 go to j
  exact run₁.trans (steps_bltz pairCode.tail (by simp) hv)

/-- The dispatcher from its j-th pair of instructions on, when RR holds k: it arrives at position
j + k.  The positions fit in a word (hn). -/
theorem steps_dispatcher_from (hcode : CodeAt code disp (dispatcher n))
    (hn : 2 * (n : ℤ) < (2 : ℤ) ^ W) (m : ℤ → BitVec W) (hone : m cONE = wd W 1) (k j : ℕ)
    (hjk : j + k < n) :
    Steps code (2 * (k + 1)) ⟨disp + 2 * j, Function.update m cRR (wd W k)⟩
      ⟨j + k, Function.update m cRR (wd W (-1))⟩ := by
  induction k generalizing j with
  | zero =>
    simpa using steps_dispatcher_pair hcode (show j < n by omega) m hone (v := 0)
      (by constructor <;> omega)
  | succ k ih =>
    have run := steps_dispatcher_pair hcode (show j < n by omega) m hone (v := k + 1)
      (by constructor <;> omega)
    rw [add_sub_cancel_right] at run
    exact ((run.trans (ih _ (by omega))).cast_count (by ring)).cast_pos (by ring)

/-- From the beginning of the dispatcher, with the position r in RR, the machine arrives at position
r after 2 (r + 1) steps; RR then holds -1, and no other cell has changed.  The positions fit in a
word (hn). -/
theorem steps_dispatcher {r : ℕ} (hcode : CodeAt code disp (dispatcher n)) (hr : r < n)
    (hn : 2 * (n : ℤ) < (2 : ℤ) ^ W) (m : ℤ → BitVec W) (hone : m cONE = wd W 1)
    (hRR : m cRR = wd W r) :
    Steps code (2 * (r + 1)) ⟨disp, m⟩ ⟨r, Function.update m cRR (wd W (-1))⟩ := by
  have := steps_dispatcher_from hcode hn m hone r 0 (by omega)
  rwa [Nat.zero_add, ← hRR, Function.update_eq_self] at this
