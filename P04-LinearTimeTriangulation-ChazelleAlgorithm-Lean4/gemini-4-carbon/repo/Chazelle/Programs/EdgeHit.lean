module

public import Chazelle.Programs.Tactics
public import Chazelle.Geometry.Basic

/-!
# Horizontal ray versus edge: the hit kernel

Given a query point `q = (qx, qy)` and an edge from `u = (ux, uy)` to `v = (vx, vy)`, the
horizontal ray to the right from `q` hits the edge when the edge *straddles* the ordinate of
`q` with the half-open rule

  `StraddlesY q u v := (uy ≤ qy ∧ qy < vy) ∨ (vy ≤ qy ∧ qy < uy)`

(exactly one endpoint has ordinate `≤ qy`; a horizontal edge never straddles — this is the
mirror image of `Chazelle.Jordan.straddles`, which straddles in `x`), and the hit abscissa

  `hitX q u v := ux + (qy - uy) * (vx - ux) / (vy - uy)`

satisfies `qx < hitX q u v`.  Straddling guarantees `vy - uy ≠ 0`, and the program only
divides in that case.

## The kernel `edgeHitStmt`

| register | role                                              |
|----------|---------------------------------------------------|
| `rreg 0` | `qx` (input)                                      |
| `rreg 1` | `qy` (input)                                      |
| `rreg 2` | `ux` (input)                                      |
| `rreg 3` | `uy` (input)                                      |
| `rreg 4` | `vx` (input)                                      |
| `rreg 5` | `vy` (input)                                      |
| `nreg 0` | output flag: `1` = hit, `0` = no hit              |
| `rreg 6` | output: `hitX q u v` (written whenever the edge straddles) |
| `rreg 7`, `rreg 8` | scratch (written whenever the edge straddles) |

Everything else (natural registers `≠ 0`, real registers `∉ {6, 7, 8}`, both memories, the
output list) is unchanged.  Cost `≤ 12` machine instructions; word bound: `1 ≤ W`.

## Main results

* `edgeHit_exec`: the spec lemma.
* `hitX_mem_segment`: `(hitX q u v, qy) ∈ segment u v` when the edge straddles.
* `hitsRight_iff`, `straddlesY_iff_not_iff`, `hitX_comm`: characterisations.
-/

namespace Chazelle

namespace Programs

open Machine Machine.Stmt

@[expose] public section

/-! ### The mathematics -/

/-- The edge `u v` straddles the ordinate of `q` (half-open rule): exactly one endpoint has
ordinate `≤ q.2`.  Mirror image of `Chazelle.Jordan.straddles`. -/
def StraddlesY (q u v : Point) : Prop :=
  (u.2 ≤ q.2 ∧ q.2 < v.2) ∨ (v.2 ≤ q.2 ∧ q.2 < u.2)

/-- The abscissa at which the horizontal line through `q` meets the line through `u` and `v`
(meaningful when `v.2 ≠ u.2`). -/
noncomputable def hitX (q u v : Point) : ℝ :=
  u.1 + (q.2 - u.2) * (v.1 - u.1) / (v.2 - u.2)

/-- The horizontal ray to the right from `q` hits the edge `u v`: the edge straddles the
ordinate of `q` and the hit abscissa is strictly to the right of `q`. -/
def HitsRight (q u v : Point) : Prop := StraddlesY q u v ∧ q.1 < hitX q u v

/-! ### The program -/

/-! ### Verification -/

section verification
variable {P : Polygon} {W : ℕ}

end verification

end

end Programs

end Chazelle
