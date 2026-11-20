module

public import PottsDiscontinuity.TorusCrossing.BdEven

/-!
# A local lemma at a primal cell

Around a primal cell `c` of a board, the (up to four) inner medial vertices of its corners carry
the dual edges `W S`, `E S`, `N W`, `N E` of the 4-cycle `W - S - E - N`.  For a label `ℓ` on odd
cells which is constant on each boundary row, if `c` sees an edge with both ends labelled and an
edge with an unlabelled end, then it sees an edge with exactly one labelled end.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

theorem local_prop (a b d n X1 X2 Y1 Y2 : Prop) :
    (¬ Y1 → (a ↔ d)) → (¬ Y2 → (a ↔ d)) →
    ((X1 ∧ Y1 ∧ ¬ (a ∧ b)) ∨ (X2 ∧ Y1 ∧ ¬ (d ∧ b)) ∨ (X1 ∧ Y2 ∧ ¬ (n ∧ a)) ∨
      (X2 ∧ Y2 ∧ ¬ (n ∧ d))) →
    ((X1 ∧ Y1 ∧ (a ∧ b)) ∨ (X2 ∧ Y1 ∧ (d ∧ b)) ∨ (X1 ∧ Y2 ∧ (n ∧ a)) ∨
      (X2 ∧ Y2 ∧ (n ∧ d))) →
    ((X1 ∧ Y1 ∧ (a ↔ ¬ b)) ∨ (X2 ∧ Y1 ∧ (d ↔ ¬ b)) ∨ (X1 ∧ Y2 ∧ (n ↔ ¬ a)) ∨
      (X2 ∧ Y2 ∧ (n ↔ ¬ d))) := by
  tauto

theorem local_vbd (R : Rect) (ℓ : Cell → Prop) (c : Cell) (hc : IsPrimal c) (hcc : c ∈ R.cells)
    (hbot : c.2 = R.y0 → (ℓ (c.1 - 1, c.2) ↔ ℓ (c.1 + 1, c.2)))
    (htop : c.2 = R.y0 + R.h → (ℓ (c.1 - 1, c.2) ↔ ℓ (c.1 + 1, c.2)))
    (h1 : ∃ e ∈ corners c, e ∈ R.inner ∧ ¬ (ℓ (dualEnds e).1 ∧ ℓ (dualEnds e).2))
    (h2 : ∃ e ∈ corners c, e ∈ R.inner ∧ (ℓ (dualEnds e).1 ∧ ℓ (dualEnds e).2)) :
    ∃ e ∈ corners c, e ∈ R.inner ∧ IsSep ℓ e := by
  have c1 := dualEnds_corner1 c hc
  have c2 := dualEnds_corner2 c hc
  have c3 := dualEnds_corner3 c hc
  have c4 := dualEnds_corner4 c hc
  have hcc' := Rect.mem_cells.1 hcc
  have i1 : c ∈ R.inner ↔ (R.x0 + 1 ≤ c.1 ∧ R.y0 + 1 ≤ c.2) := by
    rw [Rect.mem_inner]; constructor <;> intro h <;> omega
  have i2 : ((c.1 + 1, c.2) : Cell) ∈ R.inner ↔ (c.1 + 1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ c.2) := by
    rw [Rect.mem_inner]; constructor <;> intro h <;> dsimp only at * <;> omega
  have i3 : ((c.1, c.2 + 1) : Cell) ∈ R.inner ↔ (R.x0 + 1 ≤ c.1 ∧ c.2 + 1 ≤ R.y0 + R.h) := by
    rw [Rect.mem_inner]; constructor <;> intro h <;> dsimp only at * <;> omega
  have i4 : ((c.1 + 1, c.2 + 1) : Cell) ∈ R.inner ↔ (c.1 + 1 ≤ R.x0 + R.w ∧ c.2 + 1 ≤ R.y0 + R.h) := by
    rw [Rect.mem_inner]; constructor <;> intro h <;> dsimp only at * <;> omega
  simp only [corners, Finset.exists_mem_insert, Finset.mem_singleton, exists_eq_left,
    i1, i2, i3, i4, and_assoc, IsSep, c1, c2, c3, c4] at h1 h2 ⊢
  refine local_prop _ _ _ _ _ _ _ _ ?_ ?_ h1 h2
  · exact fun h => hbot (by omega)
  · exact fun h => htop (by omega)

end PottsDiscontinuity.TorusCrossing
