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

theorem primalEnds_corner1 (z : Cell) (hz : ¬ IsPrimal z) :
    primalEnds z = ((z.1 - 1, z.2), (z.1, z.2 - 1)) := by
  unfold primalEnds; unfold IsPrimal at hz
  simp_all

theorem primalEnds_corner2 (z : Cell) (hz : ¬ IsPrimal z) :
    primalEnds (z.1 + 1, z.2) = ((z.1 + 1, z.2), (z.1, z.2 - 1)) := by
  unfold primalEnds; unfold IsPrimal at hz
  rw [ite_eq_left (by omega)]
  simp

theorem primalEnds_corner3 (z : Cell) (hz : ¬ IsPrimal z) :
    primalEnds (z.1, z.2 + 1) = ((z.1, z.2 + 1), (z.1 - 1, z.2)) := by
  unfold primalEnds; unfold IsPrimal at hz
  rw [ite_eq_left (by omega)]
  simp

theorem primalEnds_corner4 (z : Cell) (hz : ¬ IsPrimal z) :
    primalEnds (z.1 + 1, z.2 + 1) = ((z.1, z.2 + 1), (z.1 + 1, z.2)) := by
  unfold primalEnds; unfold IsPrimal at hz
  rw [ite_eq_right (by omega)]
  simp

theorem card_filter_corners (p : Cell → Prop) [DecidablePred p] (c : Cell) :
    ((corners c).filter p).card =
      (if p c then 1 else 0) + (if p (c.1 + 1, c.2) then 1 else 0) +
        (if p (c.1, c.2 + 1) then 1 else 0) + (if p (c.1 + 1, c.2 + 1) then 1 else 0) := by
  unfold corners
  rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
  grind

private theorem even_indicator (p : Prop) [Decidable p] : Even (if p then 1 else 0 : ℕ) ↔ ¬p := by
  by_cases p <;> simp_all

/-- The boundary of a clipped square has even degree in the label cut if the
outer labels agree whenever the top or bottom pair of edges is missing. -/
private theorem even_clipped_cycle (w s e n lo hi : Prop) [Decidable lo] [Decidable hi]
    (hl : ¬lo → (w ↔ e))
    (hh : ¬hi → (w ↔ e)) :
    Even ((if lo ∧ (w ↔ ¬s) then 1 else 0) + (if lo ∧ (e ↔ ¬s) then 1 else 0) +
      (if hi ∧ (n ↔ ¬w) then 1 else 0) + (if hi ∧ (n ↔ ¬e) then 1 else 0) : ℕ) := by
  simp only [Nat.even_add, even_indicator]
  tauto

open Rect in
theorem even_corner_separation (R : Rect) (l : Cell → Prop) (z : Cell)
    (hx1 : R.x0 < z.1) (hx2 : z.1 < R.x0 + R.w)
    (hy1 : R.y0 ≤ z.2) (hy2 : z.2 ≤ R.y0 + R.h)
    (hbot : z.2 = R.y0 → (l (z.1 - 1, z.2) ↔ l (z.1 + 1, z.2)))
    (htop : z.2 = R.y0 + R.h → (l (z.1 - 1, z.2) ↔ l (z.1 + 1, z.2)))
    (ends : Cell → Cell × Cell)
    (h1 : ends z = ((z.1 - 1, z.2), (z.1, z.2 - 1)))
    (h2 : ends (z.1 + 1, z.2) = ((z.1 + 1, z.2), (z.1, z.2 - 1)))
    (h3 : ends (z.1, z.2 + 1) = ((z.1, z.2 + 1), (z.1 - 1, z.2)))
    (h4 : ends (z.1 + 1, z.2 + 1) = ((z.1, z.2 + 1), (z.1 + 1, z.2))) :
    Even (((corners z).filter (fun m => m ∈ R.inner ∧ (l (ends m).1 ↔ ¬l (ends m).2))).card) := by
  rw [card_filter_corners, h1, h2, h3, h4]
  have m1 : z ∈ R.inner ↔ R.y0 < z.2 := by rw [mem_inner]; omega
  have m2 : (z.1 + 1, z.2) ∈ R.inner ↔ R.y0 < z.2 := by rw [mem_inner]; dsimp only; omega
  have m3 : (z.1, z.2 + 1) ∈ R.inner ↔ z.2 < R.y0 + R.h := by rw [mem_inner]; dsimp only; omega
  have m4 : (z.1 + 1, z.2 + 1) ∈ R.inner ↔ z.2 < R.y0 + R.h := by rw [mem_inner]; dsimp only; omega
  simp only [m1, m2, m3, m4]
  exact even_clipped_cycle _ _ _ _ (R.y0 < z.2) (z.2 < R.y0 + R.h)
    (fun h => hbot (by omega)) (fun h => htop (by omega))

/-- Cut indicator of the primal edge at `m` for the vertex set `X`. -/
def IsCut (X : Cell → Prop) (m : Cell) : Prop := X (primalEnds m).1 ≠ X (primalEnds m).2

open Rect in
/-- Parity of the number of cut board edges around an odd cell strictly inside the side columns,
given equal status of the two outer neighbours on the bottom and top rows. -/
theorem cut_deg_even (R : Rect) (_hh : 0 < R.h) (X : Cell → Prop) (z : Cell) (hz : ¬ IsPrimal z)
    (hx1 : R.x0 < z.1) (hx2 : z.1 < R.x0 + R.w) (hzy1 : R.y0 ≤ z.2) (hzy2 : z.2 ≤ R.y0 + R.h)
    (hbot : z.2 = R.y0 → (X (z.1 - 1, z.2) ↔ X (z.1 + 1, z.2)))
    (htop : z.2 = R.y0 + R.h → (X (z.1 - 1, z.2) ↔ X (z.1 + 1, z.2))) :
    Even (((corners z).filter (fun m => m ∈ R.inner ∧ IsCut X m)).card) := by
  have sep (a b : Prop) : (a ≠ b) ↔ (a ↔ ¬b) := by grind
  simpa only [IsCut, sep] using
    even_corner_separation R X z hx1 hx2 hzy1 hzy2 hbot htop primalEnds
    (primalEnds_corner1 z hz) (primalEnds_corner2 z hz)
    (primalEnds_corner3 z hz) (primalEnds_corner4 z hz)

end PottsDiscontinuity.TorusCrossing
