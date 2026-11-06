module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ShootCutPos

/-!
# WP-G, part 26: keys and parameters on one walk edge

* `param_pos_iff`: the parameter of a proper position `⟨p, j + 1⟩` is positive iff the edge is
  not horizontal and the height of `Q.vtx j` differs from the one of the start of the edge
  (the test `posP`);
* `key_lt_iff`: two positions of one edge with height codes `≥ 1` are in key order iff the edge
  is not horizontal and their heights are in the order of the edge (the test `keyLess`);
* the box block of a chain model: all walk heights lie in `[-R, R]` (`walk_y_bounds`), the box
  edges `0, 2, 4` are horizontal (`box_horizontal`), and an inner position on the box edges
  `1, 3, 5` has a positive parameter (`box_param_pos`).
-/


namespace Chazelle.Core

@[expose] public section

namespace ShootCut

section
variable (M : Model) (Q : Polygon)
theorem param_succ (p j : ℕ) :
    M.param Q ⟨p, j + 1⟩ = if (M.wa p).2 = (M.wb p).2 then 0
      else ((Q.vtx j).2 - (M.wa p).2) / ((M.wb p).2 - (M.wa p).2) := rfl

/-- **A positive parameter** (`posP`). -/
theorem param_pos_iff {n p j : ℕ} (hx : ProperPos M Q n ⟨p, j + 1⟩) :
    0 < M.param Q ⟨p, j + 1⟩ ↔ ((M.wa p).2 ≠ (M.wb p).2 ∧ (M.W.vtx p).2 ≠ (Q.vtx j).2) := by
  have h0 := hx.1
  rw [param_succ] at h0 ⊢
  constructor
  · intro h
    by_cases hh : (M.wa p).2 = (M.wb p).2
    · simp_all
    · refine ⟨hh, fun hy => ?_⟩
      rw [ite_eq_right hh] at h
      have : (Q.vtx j).2 - (M.wa p).2 = 0 := by
        show (Q.vtx j).2 - (M.W.vtx p).2 = 0; simp_all
      simp_all
  · rintro ⟨hh, hy⟩
    rw [ite_eq_right hh] at h0 ⊢
    positivity

/-- **Two positions of one edge in key order** (`keyLess`). -/
theorem key_lt_iff {p h₁ h₂ : ℕ} (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) :
    M.key Q ⟨p, h₁⟩ < M.key Q ⟨p, h₂⟩ ↔ ((M.wa p).2 ≠ (M.wb p).2 ∧
      NFLoc.dirOf (Q.vtx (h₁ - 1)).2 (Q.vtx (h₂ - 1)).2 = NFLoc.dirOf (M.wa p).2 (M.wb p).2) := by
  obtain ⟨a, rfl⟩ : ∃ a, h₁ = a + 1 := ⟨h₁ - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, h₂ = b + 1 := ⟨h₂ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold Model.key
  simp only [param_succ]
  set A := (M.wa p).2
  set B := (M.wb p).2
  set y₁ := (Q.vtx a).2
  set y₂ := (Q.vtx b).2
  by_cases hh : A = B
  · simp_all
  · rw [ite_eq_right hh, ite_eq_right hh]
    unfold NFLoc.dirOf
    rcases lt_or_gt_of_ne hh with hAB | hAB
    · have hd : 0 < B - A := by linarith
      rw [ite_eq_left hAB, add_lt_add_iff_left, div_lt_div_iff_of_pos_right hd]
      ram_grind
    · have hd : B - A < 0 := by linarith
      rw [ite_eq_right (not_lt.2 hAB.le), ite_eq_left hAB, add_lt_add_iff_left,
        div_lt_div_right_of_neg hd]
      ram_grind


end

variable (C : Chain) (Q : Polygon)

theorem walk_vtx_box {q : ℕ} (hq : q ≤ 5) :
    ((chainModel C).W.vtx q).2 = C.radius ∨ ((chainModel C).W.vtx q).2 = -C.radius := by
  show ((C.sideWalk C.sideBeta).vtx q).2 = C.radius ∨ ((C.sideWalk C.sideBeta).vtx q).2 = -C.radius
  interval_cases q
  · aesop
  · aesop
  all_goals aesop

/-- **All walk heights lie in `[-R, R]`.** -/
theorem walk_y_bounds {q : ℕ} (hq : q < 2 * C.m + 7) :
    -C.radius ≤ ((chainModel C).W.vtx q).2 ∧ ((chainModel C).W.vtx q).2 ≤ C.radius := by
  have hR := C.radius_pos
  rcases (show q ≤ 5 ∨ 6 ≤ q by omega) with h | h
  · rcases walk_vtx_box C h with e | e <;> rw [e] <;> constructor <;> linarith
  · obtain ⟨i, rfl⟩ : ∃ i, q = i + 6 := ⟨q - 6, by omega⟩
    show -C.radius ≤ ((C.sideWalk C.sideBeta).vtx (i + 6)).2 ∧
      ((C.sideWalk C.sideBeta).vtx (i + 6)).2 ≤ C.radius
    rw [C.sideWalk_vtx_tour _ (by omega)]
    have hb := C.set_subset_box (C.vertex_mem_set (C.sideIdx_le C.sideBeta i))
    have := abs_lt.1 hb.2
    core_grind

/-- The box edges `0, 2, 4` are horizontal. -/
theorem box_horizontal {p : ℕ} (hp : p = 0 ∨ p = 2 ∨ p = 4) :
    ((chainModel C).wa p).2 = ((chainModel C).wb p).2 := by
  aesop

/-- **An inner position on the box edges `1, 3, 5`** has a positive parameter. -/
theorem box_param_pos {n p j : ℕ} (hp : p = 1 ∨ p = 3 ∨ p = 5)
    (hx : ProperPos (chainModel C) Q n ⟨p, j + 1⟩)
    (hin : (chainModel C).InnerPt ((chainModel C).pos Q ⟨p, j + 1⟩)) :
    0 < (chainModel C).param Q ⟨p, j + 1⟩ := by
  have hR := C.radius_pos
  have hn : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  have hm := C.one_le
  have hwa : (chainModel C).wa p = (C.sideWalk C.sideBeta).vtx p := rfl
  have hwb : (chainModel C).wb p = (C.sideWalk C.sideBeta).vtx (p + 1) := by
    unfold Model.wb; rw [hn, Nat.mod_eq_of_lt (by omega)]; rfl
  -- the edge is not horizontal
  have hnh : ((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 := by
    rw [hwa, hwb]
    rcases hp with rfl | rfl | rfl
    · rw [C.sideWalk_vtx_one, C.sideWalk_vtx_two]; linarith
    · rw [C.sideWalk_vtx_three, C.sideWalk_vtx_four]; linarith
    · rw [C.sideWalk_vtx_five, show (5 + 1 : ℕ) = 0 + 6 from rfl,
        C.sideWalk_vtx_tour _ (by omega), C.sideTour_zero]
      have := C.top_snd_lt_radius
      core_grind
  -- the point of the position is at the height of `Q.vtx j`
  have hpos : ((chainModel C).pos Q ⟨p, j + 1⟩).2 = (Q.vtx j).2 := by
    grind [Model.pos, Geometry.lerp_snd, param_succ]
  obtain ⟨⟨q, q', hq, hq', hlo, hhi⟩, -⟩ := hin
  rw [hpos] at hlo hhi
  rw [hn] at hq hq'
  have b1 := walk_y_bounds C hq
  have b2 := walk_y_bounds C hq'
  refine (param_pos_iff _ Q hx).2 ⟨hnh, ?_⟩
  show ((C.sideWalk C.sideBeta).vtx p).2 ≠ (Q.vtx j).2
  rcases hp with rfl | rfl | rfl
  · rw [C.sideWalk_vtx_one]; linarith
  · rw [C.sideWalk_vtx_three]; linarith
  · rw [C.sideWalk_vtx_five, Chazelle.Chain.slitTop_snd]; linarith

end ShootCut

end

end Chazelle.Core
