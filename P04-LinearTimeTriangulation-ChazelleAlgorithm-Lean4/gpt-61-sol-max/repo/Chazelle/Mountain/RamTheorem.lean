module

public meta import Chazelle.Arithmetic

public import Chazelle.Mountain.RamStack

/-!
# The monotone-mountain stack walk on the RAM, part 2: the walk and the whole program

This file completes the verification of `mountainStmt` (`RamStack.lean`): the walk
`outerLoop` mirrors `Chazelle.Mountain.walk`, the initialisation sets up the stack `[1, 0]`
at `k = 2`, and the sign `σ = mountainSign P = if 0 < D₀ then 1 else -1` of
`D₀ = det v_{n-1} v₀ v₁` is computed once.

## Costs

* pop loop at vertex `k` with `p` pops: `≤ 25 * (p + 1) + 2` (`innerLoop_exec`);
* one iteration of the walk: `≤ 25 * p + 31`, plus `2` of loop overhead;
* the walk from vertex `k` with stack `s`: `≤ 25 * (walk P σ k s).1.length + 33 * (n - k) + 2`
  (`outerLoop_exec`, potential `outerPot`);
* initialisation `16`, sign `≤ 10`.

Total (`mountainStmt_exec_sign`): `≤ 25 * (mountainTriangulation P σ).length + 33 * (n - 2) + 28`;
for a mountain the triangulation has `n - 2` triangles, whence `≤ 58 * n`
(`mountainStmt_exec`), and the program `mountainProgram = compile mountainStmt 0 ++ [halt]`
runs within `58 * (n + 1)` steps with words bounded by `n + 1`
(`mountainProgram_triangulates`).
-/

namespace Chazelle.Mountain

open Machine Machine.Stmt Programs
open Chazelle.EarClip (detInto detInto_exec)

@[expose] public section

section walkLoop
variable {P : Polygon} {W : ℕ}

/-! ### The walk -/

end walkLoop

/-! ### Initialisation and the sign -/

/-- The sign computed by the program: `1` if `0 < det v_{n-1} v₀ v₁`, else `-1`. -/
noncomputable def mountainSign (P : Polygon) : ℝ :=
  if 0 < det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) then 1 else -1

/-- **The computed sign is a valid orientation sign for a mountain**: `σ = ±1` and
`0 < σ * det v_{n-1} v₀ v₁` (the determinant is nonzero by `mountain_orient_det`). -/
theorem mountainSign_spec (P : Polygon) (hM : IsMountain P) :
    (mountainSign P = 1 ∨ mountainSign P = -1) ∧
      0 < mountainSign P * det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) := by
  have h := mountain_orient_det P hM
  have hne : det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) ≠ 0 := by
    intro h0; simp_all
  unfold mountainSign
  split_ifs with hpos
  all_goals ram_grind

section init
variable {P : Polygon} {W : ℕ}

end init

/-! ### The whole program -/

section main
variable {P : Polygon} {W : ℕ}

end main

end

end Chazelle.Mountain
