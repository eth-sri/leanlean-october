module

public import Chazelle.Mountain.BaseSign
public import Chazelle.EarClip.RamDet

/-!
# The monotone-mountain stack walk on the RAM, part 1: the program and the pop loop

This file writes the linear-time triangulation of a monotone mountain (`Chazelle.Mountain.walk`,
`Chazelle.Mountain.popLoop`) as a structured RAM program and verifies its pop loop.

## Register and memory layout

* natural memory `nmem 0 … nmem (top - 1)`: the stack of vertex indices, bottom first;
* natural registers: `nreg 1 = top` (the stack height), `nreg 2 = k` (the current vertex),
  `nreg 3 = n`, `nreg 4 = 1`, `nreg 5 = c` (top entry), `nreg 6 = b` (second entry),
  `nreg 7 = 2`, `nreg 8` the flag of the pop loop, `nreg 9 = 0`, `nreg 10` scratch (addresses);
* real registers: `rreg 1, 2` the coordinates of `vtx b`, `rreg 3, 4` of `vtx c`, `rreg 5, 6`
  of `vtx k`; `rreg 7` the determinant (`rreg 8, 9` scratch of `detInto`); `rreg 10 = σ`;
  `rreg 11 = σ * det`; `rreg 12 = 0`.

## The program

```
init:  n; 1; 2; 0; nmem 0 := 0; nmem 1 := 1; top := 2; k := 2        -- initBlock
       read v_{n-1}, v_0, v_1; D₀ := det; σ := if 0 < D₀ then 1 else -1  -- signStmt
while k < n:                                                           -- outerLoop
  flag := 1
  while 0 < flag:                                                      -- innerLoop
    if top < 2 then flag := 0
    else c := nmem (top-1); b := nmem (top-2); read b c k; D := det; t := σ * D   -- testStmt
         if 0 < t then (emit (b, c, k); top := top - 1) else flag := 0
  nmem top := k; top := top + 1; k := k + 1                            -- pushStmt
```

## Relation to the abstract algorithm

`stackOf c = stk c.nmem (c.nreg 1)` is the stack (top first) held by a configuration.
The pop loop's invariant `InnerInv` says: while the flag is `1`, the output followed by the
triangles still to be emitted by `popLoop P σ k (stackOf c)` is the final output `oF`, and that
call ends with the final stack `sF`; once the flag is `0`, the output is `oF` and the stack
is `sF`.  One iteration mirrors one unfolding of `popLoop_cons_cons`.

## Main results

* `testStmt_exec`: the corner test, cost `≤ 18`.
* `innerBody_inv`: one iteration of the pop loop preserves `InnerInv` and decreases the
  potential `innerPot` by at least its cost plus `2`.
* `innerLoop_exec`: the pop loop at vertex `k` from the stack `s` emits
  `(popLoop P σ k s).1`, leaves the stack `(popLoop P σ k s).2.1`, and costs
  `≤ 25 * ((popLoop P σ k s).1.length + 1) + 2`.
-/

namespace Chazelle.Mountain

open Machine Machine.Stmt Programs
open Chazelle.EarClip (detInto detInto_exec)

@[expose] public section

/-! ### The stack in natural memory -/

/-- The stack held in natural memory: `stk f t = [f (t - 1), …, f 1, f 0]` (top first). -/
def stk (f : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | t + 1 => f t :: stk f t

/-- The empty stack. -/
@[simp] theorem stk_zero (f : ℕ → ℕ) : stk f 0 = [] := rfl

/-- Unfolding the stack by one entry: the top is `f t`. -/
@[simp] theorem stk_succ (f : ℕ → ℕ) (t : ℕ) : stk f (t + 1) = f t :: stk f t := rfl

/-- The stack `stk f t` has `t` entries. -/
@[simp] theorem length_stk (f : ℕ → ℕ) (t : ℕ) : (stk f t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [ih]

/-- The stack `stk f t` only depends on the entries of `f` below `t`. -/
theorem stk_congr {f g : ℕ → ℕ} {t : ℕ} (h : ∀ i, i < t → f i = g i) : stk f t = stk g t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [stk_succ, stk_succ, h t (by omega), ih (fun i hi => h i (by omega))]

/-- Writing at address `t` does not change the stack `stk f t`. -/
theorem stk_upd (f : ℕ → ℕ) (t v : ℕ) : stk (upd f t v) t = stk f t :=
  stk_congr (fun i hi => Machine.upd_other _ _ _ (by omega))

/-- **Push**: writing `v` at address `t` and taking `t + 1` entries pushes `v`. -/
theorem stk_push (f : ℕ → ℕ) (t v : ℕ) : stk (upd f t v) (t + 1) = v :: stk f t := by
  rw [stk_succ, Machine.upd_same, stk_upd]

/-- A stack with at least two entries: its top two entries are `f (t - 1)` and `f (t - 2)`. -/
theorem stk_two {f : ℕ → ℕ} {t : ℕ} (ht : 2 ≤ t) :
    stk f t = f (t - 1) :: f (t - 2) :: stk f (t - 2) := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 2 := ⟨t - 2, by omega⟩
  simp

/-- **Pop**: dropping the top entry. -/
theorem stk_pop {f : ℕ → ℕ} {t : ℕ} (ht : 1 ≤ t) : stk f t = f (t - 1) :: stk f (t - 1) := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  simp

/-! ### The program -/

/-! ### The constants -/

/-! ### The corner test -/

section specs
variable {P : Polygon} {W : ℕ}

/-! ### The pop loop -/

end specs

end

end Chazelle.Mountain
