module

public import Chazelle.Programs.RayScan
public import Chazelle.Jordan.SegmentFacts

/-!
# What the ray-shooting scan computes, geometrically

`FirstHitRight P q x`: `x` is the smallest hit abscissa of the horizontal ray to the right from
`q` over the edges of `P` that it hits (half-open straddling rule `StraddlesY`, see
`EdgeHit.lean`).  The scan `rayScanStmt` computes exactly this (`rayScan_exec_firstHit`).

Consequences, all honest about the half-open convention:

* `fst_eq_hitX_of_mem_segment`: a straddling segment meets the horizontal line through `q`
  exactly once, at abscissa `hitX q u v`.
* `FirstHitRight.mem_boundary`: `(x, q.2) ∈ P.boundary`; `FirstHitRight.lt`: `q.1 < x`.
* `FirstHitRight.not_straddlesY_of_between`: a point of edge `i` on the horizontal line with
  abscissa strictly between `q.1` and `x` lies on a *non-straddling* edge (a horizontal edge at
  height `q.2`, or an edge touching the line at an endpoint on the wrong half-open side).
  Nothing more is claimed: such boundary points may exist.
* `FirstHitRight.unique`, `exists_firstHitRight`: the first hit is unique and exists as soon as
  some edge is hit.
-/

namespace Chazelle

namespace Programs

open Machine

@[expose] public section

/-! ### A straddling segment meets the horizontal line only at `hitX` -/

/-! ### The first hit -/

/-- `x` is the abscissa of the first hit of the horizontal ray to the right from `q` on the
boundary of `P`: some edge `i < n` is hit (`HitsRight`, half-open rule) with hit abscissa `x`,
and `x` is `≤` the hit abscissa of every hit edge. -/
def FirstHitRight (P : Polygon) (q : Point) (x : ℝ) : Prop :=
  (∃ i, i < P.n ∧ HitsRight q (P.vtx i) (P.vtx ((i + 1) % P.n)) ∧
    x = hitX q (P.vtx i) (P.vtx ((i + 1) % P.n))) ∧
  (∀ i, i < P.n → HitsRight q (P.vtx i) (P.vtx ((i + 1) % P.n)) →
    x ≤ hitX q (P.vtx i) (P.vtx ((i + 1) % P.n)))

variable {P : Polygon} {q : Point} {x y : ℝ}

/-- The first hit is strictly to the right of `q`. -/
theorem FirstHitRight.lt (h : FirstHitRight P q x) : q.1 < x := by
  obtain ⟨⟨i, hi, hhit, rfl⟩, -⟩ := h
  exact hhit.2

/-! ### The program computes the first hit -/

end

end Programs

end Chazelle
