module

public import PottsDiscontinuity.TorusCrossing.Planar

/-!
# Parity of a vertex cut around an odd cell

For a set `X` of primal cells, an edge of the board is *cut* when exactly one of its ends lies in
`X`.  Around every odd cell the four primal edges form a 4-cycle, so the number of cut edges at an
odd cell is even.  Cells on the bottom or top row see only two of their four edges; the parity
there is the difference of the `X`-statuses of the two outer primal neighbours.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open scoped Classical

section
variable (z : Cell) (hz : ¬ IsPrimal z)
include z hz
theorem primalEnds_corner1  :
    primalEnds z = ((z.1 - 1, z.2), (z.1, z.2 - 1)) := by
  simp_all [primalEnds, IsPrimal]

theorem primalEnds_corner2  :
    primalEnds (z.1 + 1, z.2) = ((z.1 + 1, z.2), (z.1, z.2 - 1)) := by
  grind [primalEnds, IsPrimal]

theorem primalEnds_corner3  :
    primalEnds (z.1, z.2 + 1) = ((z.1, z.2 + 1), (z.1 - 1, z.2)) := by
  grind [primalEnds, IsPrimal]

theorem primalEnds_corner4  :
    primalEnds (z.1 + 1, z.2 + 1) = ((z.1, z.2 + 1), (z.1 + 1, z.2)) := by
  grind [primalEnds, IsPrimal]
end

theorem card_filter_corners (p : Cell → Prop) [DecidablePred p] (c : Cell) :
    ((corners c).filter p).card =
      (if p c then 1 else 0) + (if p (c.1 + 1, c.2) then 1 else 0) +
        (if p (c.1, c.2 + 1) then 1 else 0) + (if p (c.1 + 1, c.2 + 1) then 1 else 0) := by
  unfold corners
  rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
  grind

/-- Cut indicator of the primal edge at `m` for the vertex set `X`. -/
def IsCut (X : Cell → Prop) (m : Cell) : Prop := X (primalEnds m).1 ≠ X (primalEnds m).2

open Rect in
/-- Parity of the number of cut board edges around an odd cell strictly inside the side columns,
given equal status of the two outer neighbours on the bottom and top rows. -/
theorem cut_deg_even (R : Rect) (hh : 0 < R.h) (X : Cell → Prop) (z : Cell) (hz : ¬ IsPrimal z)
    (hx1 : R.x0 < z.1) (hx2 : z.1 < R.x0 + R.w) (hzy1 : R.y0 ≤ z.2) (hzy2 : z.2 ≤ R.y0 + R.h)
    (hbot : z.2 = R.y0 → (X (z.1 - 1, z.2) ↔ X (z.1 + 1, z.2)))
    (htop : z.2 = R.y0 + R.h → (X (z.1 - 1, z.2) ↔ X (z.1 + 1, z.2))) :
    Even (((corners z).filter (fun m => m ∈ R.inner ∧ IsCut X m)).card) := by
  have hh' : (0 : ℤ) < R.h := by omega
  rw [card_filter_corners]
  unfold IsCut
  rw [primalEnds_corner1 z hz, primalEnds_corner2 z hz, primalEnds_corner3 z hz,
    primalEnds_corner4 z hz]
  simp only [mem_inner]
  by_cases hb : z.2 = R.y0
  · grind
  · by_cases ht : z.2 = R.y0 + R.h
    · grind
    · have e1 : (R.x0 + 1 ≤ z.1 ∧ z.1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ z.2 ∧ z.2 ≤ R.y0 + R.h) := by omega
      have e2 : (R.x0 + 1 ≤ z.1 + 1 ∧ z.1 + 1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ z.2 ∧ z.2 ≤ R.y0 + R.h) := by omega
      have e3 : (R.x0 + 1 ≤ z.1 ∧ z.1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ z.2 + 1 ∧ z.2 + 1 ≤ R.y0 + R.h) := by omega
      have e4 : (R.x0 + 1 ≤ z.1 + 1 ∧ z.1 + 1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ z.2 + 1 ∧ z.2 + 1 ≤ R.y0 + R.h) := by omega
      simp only [e1, e2, e3, true_and]
      grind

end PottsDiscontinuity.TorusCrossing
