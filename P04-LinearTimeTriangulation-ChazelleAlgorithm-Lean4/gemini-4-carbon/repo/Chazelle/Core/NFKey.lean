module

public import Chazelle.Core.SpecBase

/-!
# Walk keys reduce to height comparisons (WP-C, review finding F11)

The normal-form toolkit orders walk positions by their keys `M.key Q x = x.edge + M.param Q x`.
The machine cannot compute parameters (they are quotients of heights of the sheared polygon
`Q`), so every key comparison must reduce to comparisons of edge indices and of **heights**, which
the sign kernel decides (test `1` on symbolic points; box corners and slit ends have known
heights).  This file proves the reduction, for every model and every walk edge:

* `Model.hgtY`: the height of a walk position (the start vertex's height for code `0`, the height
  of vertex `h` of `Q` for code `h + 1`); `pos_snd` shows it is the height of its point on a
  non-horizontal edge;
* on a **horizontal** walk edge (box edges, horizontal host edges) every position has parameter
  `0` (`param_horizontal`), so all positions on it have the same key (`key_eq_of_horizontal`);
* on a **non-horizontal** walk edge the parameter is `(hgtY - y_a) / (y_b - y_a)` (`param_eq`), so
  two positions compare like their heights, in the direction of the edge
  (`key_lt_key_iff_of_same_edge`);
* positions whose parameter lies in `[0, 1)` (the positions of the walk proper) compare
  lexicographically by (edge, parameter) (`key_lt_key_iff_lex`), and membership in `[0, 1)` is a
  pair of height comparisons (`param_mem_Ico_iff`).
-/

namespace Chazelle.Core

namespace Model

@[expose] public section

variable (M : Model) (Q : Polygon)

/-- The height of a walk position: the height of the start vertex of its walk edge for code `0`,
the height of vertex `h` of `Q` for code `h + 1`. -/
noncomputable def hgtY (x : WPos) : ℝ :=
  match x.hgt with
  | 0 => (M.wa x.edge).2
  | h + 1 => (Q.vtx h).2

variable {M Q}

/-- On a horizontal walk edge every position has parameter `0`. -/
theorem param_horizontal {x : WPos} (h : (M.wa x.edge).2 = (M.wb x.edge).2) :
    M.param Q x = 0 := by
  unfold param
  rcases x with ⟨e, _ | k⟩
  · rfl
  · simp only at h ⊢
    rw [ite_eq_left h]

/-- **The parameter on a non-horizontal walk edge** is the relative height. -/
theorem param_eq {x : WPos} (h : (M.wa x.edge).2 ≠ (M.wb x.edge).2) :
    M.param Q x = (M.hgtY Q x - (M.wa x.edge).2) / ((M.wb x.edge).2 - (M.wa x.edge).2) := by
  unfold param hgtY
  rcases x with ⟨e, _ | k⟩
  · simp
  · simp only at h ⊢
    rw [ite_eq_right h]

/-- The point of a position on a non-horizontal walk edge lies at the height of the position. -/
theorem pos_snd {x : WPos} (h : (M.wa x.edge).2 ≠ (M.wb x.edge).2) :
    (M.pos Q x).2 = M.hgtY Q x := by
  unfold pos
  rw [Geometry.lerp_snd, param_eq h]
  have : (M.wb x.edge).2 - (M.wa x.edge).2 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  field_simp
  ring

/-- **Keys on a horizontal walk edge** are all equal to the edge index. -/
theorem key_eq_of_horizontal {x : WPos} (h : (M.wa x.edge).2 = (M.wb x.edge).2) :
    M.key Q x = x.edge := by
  unfold key
  rw [param_horizontal h, add_zero]

/-- **Keys on one non-horizontal walk edge** compare like heights, in the direction of the edge
(increasing on an upward edge, decreasing on a downward one). -/
theorem key_lt_key_iff_of_same_edge {x y : WPos} (he : x.edge = y.edge)
    (h : (M.wa x.edge).2 ≠ (M.wb x.edge).2) :
    M.key Q x < M.key Q y ↔
      ((M.wa x.edge).2 < (M.wb x.edge).2 ∧ M.hgtY Q x < M.hgtY Q y) ∨
        ((M.wb x.edge).2 < (M.wa x.edge).2 ∧ M.hgtY Q y < M.hgtY Q x) := by
  have hy : (M.wa y.edge).2 ≠ (M.wb y.edge).2 := he ▸ h
  unfold key
  rw [param_eq h, param_eq hy, ← he, add_lt_add_iff_left]
  set a := (M.wa x.edge).2
  set b := (M.wb x.edge).2
  rcases lt_or_gt_of_ne h with hab | hab
  · have hd : 0 < b - a := sub_pos.2 hab
    rw [div_lt_div_iff_of_pos_right hd, sub_lt_sub_iff_right]
    constructor
    · intro h'; exact Or.inl ⟨hab, h'⟩
    · rintro (⟨-, h'⟩ | ⟨h', -⟩)
      · exact h'
      · exact absurd h' (not_lt.2 hab.le)
  · have hd : b - a < 0 := sub_neg.2 hab
    rw [div_lt_div_right_of_neg hd, sub_lt_sub_iff_right]
    constructor
    · intro h'; exact Or.inr ⟨hab, h'⟩
    · rintro (⟨h', -⟩ | ⟨-, h'⟩)
      · exact absurd h' (not_lt.2 hab.le)
      · exact h'

/-- A position with code `0` is the start of its walk edge (parameter `0`). -/
theorem param_code_zero (e : ℕ) : M.param Q ⟨e, 0⟩ = 0 := rfl

end

end Model

end Chazelle.Core
