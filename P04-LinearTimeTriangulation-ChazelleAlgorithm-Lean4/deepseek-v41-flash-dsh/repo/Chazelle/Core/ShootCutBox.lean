module

public import Chazelle.Golf

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

set_option linter.unusedSimpArgs false

namespace Chazelle.Core

@[expose] public section

namespace ShootCut

theorem param_succ (M : Model) (Q : Polygon) (p j : ℕ) :
    M.param Q ⟨p, j + 1⟩ = if (M.wa p).2 = (M.wb p).2 then 0
      else ((Q.vtx j).2 - (M.wa p).2) / ((M.wb p).2 - (M.wa p).2) := rfl

/-- **A positive parameter** (`posP`). -/
theorem param_pos_iff (M : Model) (Q : Polygon) {n p j : ℕ} (hx : ProperPos M Q n ⟨p, j + 1⟩) :
    0 < M.param Q ⟨p, j + 1⟩ ↔ ((M.wa p).2 ≠ (M.wb p).2 ∧ (M.W.vtx p).2 ≠ (Q.vtx j).2) := by
  have h0 := hx.1
  rw [param_succ] at h0 ⊢
  constructor
  · intro h
    by_cases hh : (M.wa p).2 = (M.wb p).2
    · rw [ite_eq_left hh] at h; exact absurd h (lt_irrefl 0)
    · refine ⟨hh, fun hy => ?_⟩
      rw [ite_eq_right hh] at h
      have : (Q.vtx j).2 - (M.wa p).2 = 0 := by
        show (Q.vtx j).2 - (M.W.vtx p).2 = 0; rw [hy]; ring
      rw [this, zero_div] at h
      exact lt_irrefl 0 h
  · rintro ⟨hh, hy⟩
    rw [ite_eq_right hh] at h0 ⊢
    refine lt_of_le_of_ne h0 (fun h => ?_)
    have hd : (M.wb p).2 - (M.wa p).2 ≠ 0 := sub_ne_zero.2 (Ne.symm hh)
    have hn : (Q.vtx j).2 - (M.wa p).2 ≠ 0 := sub_ne_zero.2 (fun e => hy e.symm)
    exact div_ne_zero hn hd h.symm

/-- **Two positions of one edge in key order** (`keyLess`). -/
theorem key_lt_iff (M : Model) (Q : Polygon) {p h₁ h₂ : ℕ} (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) :
    M.key Q ⟨p, h₁⟩ < M.key Q ⟨p, h₂⟩ ↔ ((M.wa p).2 ≠ (M.wb p).2 ∧
      NFLoc.dirOf (Q.vtx (h₁ - 1)).2 (Q.vtx (h₂ - 1)).2 = NFLoc.dirOf (M.wa p).2 (M.wb p).2) := by
  obtain ⟨a, rfl⟩ : ∃ a, h₁ = a + 1 := ⟨h₁ - 1, ⋄⟩
  obtain ⟨b, rfl⟩ : ∃ b, h₂ = b + 1 := ⟨h₂ - 1, ⋄⟩
  ϴ Nat.add_sub_cancel
  unfold Model.key
  ϴ param_succ
  set A := (M.wa p).2
  set B := (M.wb p).2
  set y₁ := (Q.vtx a).2
  set y₂ := (Q.vtx b).2
  by_cases hh : A = B
  · Ξ ite_eq_left hh, ite_eq_left hh
    simp only [lt_irrefl, false_iff, not_and, not_not]; intro h; exact absurd hh h
  · Ξ ite_eq_right hh, ite_eq_right hh
    unfold NFLoc.dirOf
    rcases lt_or_gt_of_ne hh with hAB | hAB
    · have hd : 0 < B - A := ⟡
      Ξ ite_eq_left hAB, add_lt_add_iff_left, div_lt_div_iff_of_pos_right hd
      constructor
      · intro h; refine ⟨hh, ?_⟩; rw [ite_eq_left (⟡)]
      · rintro ⟨-, h⟩
        by_contra hc
        push Not at hc
        split_ifs at h with h1 h2 <;> first | omega | linarith
    · have hd : B - A < 0 := ⟡
      rw [ite_eq_right (not_lt.2 hAB.le), ite_eq_left hAB, add_lt_add_iff_left,
        div_lt_div_right_of_neg hd]
      constructor
      · intro h; refine ⟨hh, ?_⟩
        rw [ite_eq_right (⟡), ite_eq_left (by linarith)]
      · rintro ⟨-, h⟩
        by_contra hc
        push Not at hc
        split_ifs at h with h1 h2 <;> first | omega | linarith

variable (C : Chain) (Q : Polygon)

theorem walk_vtx_box {q : ℕ} (hq : q ≤ 5) :
    ((chainModel C).W.vtx q).2 = C.radius ∨ ((chainModel C).W.vtx q).2 = -C.radius := by
  show ((C.sideWalk C.sideBeta).vtx q).2 = C.radius ∨ ((C.sideWalk C.sideBeta).vtx q).2 = -C.radius
  interval_cases q
  · left; rw [C.sideWalk_vtx_zero]; rfl
  · left; rw [C.sideWalk_vtx_one]
  · right; rw [C.sideWalk_vtx_two]
  · right; rw [C.sideWalk_vtx_three]
  · left; rw [C.sideWalk_vtx_four]
  · left; rw [C.sideWalk_vtx_five]; rfl

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
    unfold Chazelle.Chain.sideTour
    constructor <;> linarith [this.1, this.2]

/-- The box edges `0, 2, 4` are horizontal. -/
theorem box_horizontal {p : ℕ} (hp : p = 0 ∨ p = 2 ∨ p = 4) :
    ((chainModel C).wa p).2 = ((chainModel C).wb p).2 := by
  have hn : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  unfold Model.wa Model.wb
  Ξ hn
  show ((C.sideWalk C.sideBeta).vtx p).2 = ((C.sideWalk C.sideBeta).vtx ((p + 1) % (2 * C.m + 7))).2
  rcases hp with rfl | rfl | rfl
  · rw [Nat.mod_eq_of_lt (⋄), C.sideWalk_vtx_zero, C.sideWalk_vtx_one]; rfl
  · rw [Nat.mod_eq_of_lt (⋄), C.sideWalk_vtx_two, C.sideWalk_vtx_three]
  · rw [Nat.mod_eq_of_lt (⋄), C.sideWalk_vtx_four, C.sideWalk_vtx_five]; rfl

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
    unfold Model.wb; rw [hn, Nat.mod_eq_of_lt (⋄)]; rfl
  -- the edge is not horizontal
  have hnh : ((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 := by
    Ξ hwa, hwb
    rcases hp with rfl | rfl | rfl
    · rw [C.sideWalk_vtx_one, C.sideWalk_vtx_two]; simp only; intro h; linarith
    · rw [C.sideWalk_vtx_three, C.sideWalk_vtx_four]; simp only; intro h; linarith
    · rw [C.sideWalk_vtx_five, show (5 + 1 : ℕ) = 0 + 6 from rfl,
        C.sideWalk_vtx_tour _ (⋄), C.sideTour_zero]
      have := C.top_snd_lt_radius
      intro h; rw [Chazelle.Chain.slitTop_snd] at h; linarith
  -- the point of the position is at the height of `Q.vtx j`
  have hpos : ((chainModel C).pos Q ⟨p, j + 1⟩).2 = (Q.vtx j).2 := by
    unfold Model.pos
    Ξ Geometry.lerp_snd, param_succ, ite_eq_right hnh
    have hd : ((chainModel C).wb p).2 - ((chainModel C).wa p).2 ≠ 0 :=
      sub_ne_zero.2 (Ne.symm hnh)
    field_simp
    ring
  obtain ⟨⟨q, q', hq, hq', hlo, hhi⟩, -⟩ := hin
  rw [hpos] at hlo hhi
  rw [hn] at hq hq'
  have b1 := walk_y_bounds C hq
  have b2 := walk_y_bounds C hq'
  refine (param_pos_iff _ Q hx).2 ⟨hnh, ?_⟩
  show ((C.sideWalk C.sideBeta).vtx p).2 ≠ (Q.vtx j).2
  rcases hp with rfl | rfl | rfl
  · rw [C.sideWalk_vtx_one]; intro h; simp only at h; linarith [b2.2]
  · rw [C.sideWalk_vtx_three]; intro h; simp only at h; linarith [b1.1]
  · rw [C.sideWalk_vtx_five, Chazelle.Chain.slitTop_snd]; intro h; linarith [b2.2]

end ShootCut

end

end Chazelle.Core
