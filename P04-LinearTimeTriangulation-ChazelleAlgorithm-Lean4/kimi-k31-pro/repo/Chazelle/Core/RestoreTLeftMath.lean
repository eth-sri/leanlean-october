module

public import Chazelle.Core.RestoreTValidMath

/-!
# WP-E, the candidate test on the RAM, part 17: the sector test from turn signs

For a horizontal direction the left sector of the walk is decided by signs:

* inside a (non-horizontal) walk edge, the direction points into the left sector iff the turn from
  the edge to it is positive (`left_inside_iff`);
* at a walk vertex whose two neighbours are at other heights, iff both turns are positive for a
  convex corner (positive orientation of `a, v, b`), and iff one of them is otherwise
  (`sector_horiz`, `left_vertex_iff`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Chain (sideLeft sideLeftOf sideCcw sideCross sideDot sidePt sideLeft_zero)
open Chazelle.Visibility (rayPt)
open Chazelle.Geometry (point_ext)

/-- **The corner sector for a horizontal direction.** -/
theorem sector_horiz {a v b : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hb : b.2 ≠ v.2)
    (ha : a.2 ≠ v.2) :
    sideLeftOf a v b (rayPt v σ 1) ↔
      (0 < sideCross (b - v) (a - v) ∧ 0 < sideCross (b - v) ((σ, 0) : Point) ∧
        0 < sideCross ((σ, 0) : Point) (a - v)) ∨
      (¬ 0 < sideCross (b - v) (a - v) ∧ (0 < sideCross (b - v) ((σ, 0) : Point) ∨
        0 < sideCross ((σ, 0) : Point) (a - v))) := by
  have hX : rayPt v σ 1 - v = ((σ, 0) : Point) := by
    apply point_ext <;> simp [rayPt]
  unfold sideLeftOf sideCcw
  rw [hX]
  obtain ⟨b1, b2⟩ := b
  obtain ⟨a1, a2⟩ := a
  obtain ⟨v1, v2⟩ := v
  simp only [sideCross, sideDot, Prod.fst_sub, Prod.snd_sub, ne_eq] at hb ha ⊢
  have hB  := sub_ne_zero.2 hb
  have hA  := sub_ne_zero.2 ha
  set B1 := b1 - v1
  set B2 := b2 - v2
  set A1 := a1 - v1
  set A2 := a2 - v2
  have hS : 0 < A1 ^ 2 + A2 ^ 2 := by positivity
  have hA2 : 0 < A2 ^ 2 := by positivity
  have hBA  := mul_ne_zero hB hA
  rcases lt_trichotomy (B1 * A2 - B2 * A1) 0 with hd | hd | hd
  · -- reflex
    constructor
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
      · linarith
      · exact Or.inr ⟨by linarith, h2⟩
      · linarith
      · linarith
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · linarith
      · exact Or.inr (Or.inl ⟨hd, h2⟩)
  · -- collinear
    have hcol : B1 * A2 = B2 * A1 := by linarith
    have hdot : (B1 * A1 + B2 * A2) * A2 ^ 2 = B2 * A2 * (A1 ^ 2 + A2 ^ 2) := by
      linear_combination (A1 * A2) * hcol
    have hdpos : 0 < B1 * A1 + B2 * A2 ↔ 0 < B2 * A2 := by
      constructor
      · intro h; have := mul_pos h hA2; rw [hdot] at this
        exact (mul_pos_iff_of_pos_right hS).1 this
      · intro h; have := mul_pos h hS; rw [← hdot] at this
        exact (mul_pos_iff_of_pos_right hA2).1 this
    have hdneg : B1 * A1 + B2 * A2 < 0 ↔ B2 * A2 < 0 := by
      constructor
      · intro h
        have : (B1 * A1 + B2 * A2) * A2 ^ 2 < 0 := mul_neg_of_neg_of_pos h hA2
        rw [hdot] at this
        by_contra hc; push Not at hc
        exact absurd this (not_lt.2 (mul_nonneg hc hS.le))
      · intro h
        have : B2 * A2 * (A1 ^ 2 + A2 ^ 2) < 0 := mul_neg_of_neg_of_pos h hS
        rw [← hdot] at this
        by_contra hc; push Not at hc
        exact absurd this (not_lt.2 (mul_nonneg hc hA2.le))
    rcases hσ with rfl | rfl <;>
    · constructor
      · rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨-, h2, -⟩)
        · linarith
        · linarith
        · exact Or.inr ⟨by linarith, Or.inl h3⟩
        · refine Or.inr ⟨by linarith, ?_⟩
          have hp := hdpos.1 h2
          rcases lt_or_gt_of_ne hB with hb' | hb' <;> rcases lt_or_gt_of_ne hA with ha' | ha' <;>
            first | (left; nlinarith) | (right; nlinarith)
      · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · linarith
        · rcases lt_or_gt_of_ne (show B2 * A2 ≠ 0 from hBA) with hn | hp
          · refine Or.inr (Or.inr (Or.inl ⟨by linarith, hdneg.2 hn, ?_⟩))
            rcases lt_or_gt_of_ne hB with hb' | hb' <;> rcases lt_or_gt_of_ne hA with ha' | ha' <;>
              rcases h2 with h2 | h2 <;> first | linarith | nlinarith
          · refine Or.inr (Or.inr (Or.inr ⟨by linarith, hdpos.2 hp, Or.inl ?_⟩))
            intro h; apply hB; linarith
  · -- convex
    constructor
    · rintro (⟨-, h2, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
      · exact Or.inl ⟨hd, h2, h3⟩
      · linarith
      · linarith
      · linarith
    · rintro (⟨-, h2, h3⟩ | ⟨h1, -⟩)
      · exact Or.inl ⟨hd, h2, h3⟩
      · exact absurd hd h1


/-- **Inside a walk edge** the sector test is the turn from the edge. -/
theorem left_inside_iff {M : Model} {P : Polygon} {x : WPos} {σb : ℕ}
    (h0 : 0 < M.param (Qof P) x) (h1 : M.param (Qof P) x < 1) :
    LeftB M P x σb ↔ TurnNB M x σb := by
  unfold LeftB TurnNB
  have hne := SweepPrim.ne_of_param_pos h0
  rw [SweepPrim.pos_eq_sidePt, SweepPrim.sideLeft_interior h0 h1 hne]
  unfold sideCross
  simp only [Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> linarith

/-- **At a walk vertex** whose neighbours are at other heights the sector test is decided by the
orientation of the corner and the two turns. -/
theorem left_vertex_iff {M : Model} {P : Polygon} {x : WPos} {σb : ℕ}
    (h0 : M.param (Qof P) x = 0)
    (hb : (M.W.vtx ((x.edge + 1) % M.W.n)).2 ≠ (M.W.vtx x.edge).2)
    (ha : (M.W.vtx ((x.edge + M.W.n - 1) % M.W.n)).2 ≠ (M.W.vtx x.edge).2) :
    LeftB M P x σb ↔
      (0 < sideCross (M.W.vtx ((x.edge + 1) % M.W.n) - M.W.vtx x.edge)
          (M.W.vtx ((x.edge + M.W.n - 1) % M.W.n) - M.W.vtx x.edge) ∧
        TurnNB M x σb ∧ TurnPB M x σb) ∨
      (¬ 0 < sideCross (M.W.vtx ((x.edge + 1) % M.W.n) - M.W.vtx x.edge)
          (M.W.vtx ((x.edge + M.W.n - 1) % M.W.n) - M.W.vtx x.edge) ∧
        (TurnNB M x σb ∨ TurnPB M x σb)) := by
  unfold LeftB TurnNB TurnPB
  rw [SweepPrim.pos_eq_sidePt, h0, sideLeft_zero, Chazelle.Chain.sidePt_zero]
  exact sector_horiz (dirOf_pm σb) hb ha

end

end Restore

end Chazelle.Core
