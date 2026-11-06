/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ThreeSumApsp.Programs.Tasks

/-!
# The two tasks between Negative Triangle and the (min,+)-product

[VW18, Theorem 4.2], one of the reductions behind Theorem 21(b), goes from
deciding Negative Triangle to the (min,+)-product in three steps: finding a negative triangle
([VW18, Lemma 4.1]), finding for all pairs `(i, j)` at once whether some `k` has `X[i,k] + Y[k,j] <
V[i,j]`, and a search for all entries of the product at once.  Each step is a host over an arbitrary
solver of the task below it (isHost_find, isHost_pairs, isHost_mp).  This file fixes the two tasks
in the middle, findTask and pairsTask.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3



/-- Three `n × n` matrices, and the place for `n²` flags. -/
structure PairsInst where
  (n U x y v out : ℕ)
  (X Y V : List ℤ)

/-- The three matrices and the place for the flags lie below the free pointer; the place for the
flags does not meet the matrices. -/
structure PairsInst.Pre (q : PairsInst) (μ : Light.Memory) (fr : ℕ) : Prop where
  n_pos : 1 ≤ q.n
  U_pos : 1 ≤ q.U
  lenX : q.X.length = q.n * q.n
  lenY : q.Y.length = q.n * q.n
  lenV : q.V.length = q.n * q.n
  segX : Seg μ q.x q.X
  segY : Seg μ q.y q.Y
  segV : Seg μ q.v q.V
  leX : AbsLe q.X q.U
  leY : AbsLe q.Y q.U
  leV : AbsLe q.V q.U
  belowX : q.x + q.n * q.n ≤ fr
  belowY : q.y + q.n * q.n ≤ fr
  belowV : q.v + q.n * q.n ≤ fr
  belowOut : q.out + q.n * q.n ≤ fr
  apartX : Apart q.x (q.n * q.n) q.out (q.n * q.n)

/-- The flags: cell `i n + j` holds 1 if `X[i,k] + Y[k,j] < V[i,j]` for some `k < n`, and 0 if
not. -/
noncomputable def pairFlags n (X Y V : List ℤ) :=
  (List.range (n * n)).map fun q =>
    flag (∃ k < n, X.getD (q / n * n + k) 0 + Y.getD (k * n + q % n) 0 < V.getD q 0)

/-- **All pairs**: allPairs(n, U, x, y, v, out, fr) writes the `n²` flags to out. -/
noncomputable def pairsTask : Task where
  Inst := PairsInst
  size q := q.n
  bound q := q.U
  args q := [q.n, q.U, q.x, q.y, q.v, q.out]
  Pre := PairsInst.Pre
  Post q μ fr _ μ' := Seg μ' q.out (pairFlags q.n q.X q.Y q.V) ∧ KeptBut μ μ' fr q.out (q.n * q.n)

end Light.Sec3
