module

public import Chazelle.Core.FuseAsmGeo
public import Chazelle.Core.FuseAsmCover

/-!
# WP-F fusion assembly, part 16: the input positions of the point queries

* A chain vertex `k` is the point of the walk position `(6 + tpos C k, 0)` (`vpos`).
* The cap origin is the point of the walk position `(e, h + 1)` on the far arm, where `h` is a
  vertex of `Q` at the height of the nearer neighbour: on `C₁` (walk edge from `v` to `u`) if the
  nearer arm is `w` (`capPos₀`), on `C₂` (walk edge from `v` to `w`) otherwise (`capPos₁`).
  The position is proper and the origin lies on the chain.
-/

namespace Chazelle.Core

namespace FuseAsm

@[expose] public section

open WalkEmbed
open Chazelle.Chain (sideE)

theorem walk_vtx_tpos (C : Chain) {k : ℕ} (hk : k ≤ C.m) :
    (chainModel C).W.vtx (6 + tpos C k) = C.vertex k := by
  have hn := cm_n C
  have hτ := tpos_lt C k
  have := walk_tour C k 0 (by omega)
  rw [Nat.add_zero, Nat.mod_eq_of_lt (by rw [hn]; omega)] at this
  rw [this]
  unfold tourV
  rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  unfold sideE; rw [ite_eq_left hk]

/-- **A chain vertex as a walk position.** -/
theorem vpos (C : Chain) (Q : Polygon) {k : ℕ} (hk : k ≤ C.m) :
    (chainModel C).pos Q ⟨6 + tpos C k, 0⟩ = C.vertex k := by
  unfold Model.pos
  rw [show (chainModel C).param Q ⟨6 + tpos C k, 0⟩ = 0 from rfl, Geometry.lerp_zero]
  exact walk_vtx_tpos C hk

theorem vpos_edge (C : Chain) (k : ℕ) : 6 + tpos C k < (chainModel C).W.n := by
  have := tpos_lt C k; rw [cm_n]; omega

theorem lerp_mem_set (C : Chain) {k : ℕ} (hk : k < C.m) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Geometry.lerp (C.vertex k) (C.vertex (k + 1)) t ∈ C.set :=
  ⟨k, hk, by rw [C.chainEdge_eq]; exact Geometry.lerp_mem_segment _ _ h0 h1⟩

theorem lerp_mem_set' (C : Chain) {k : ℕ} (hk : k < C.m) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Geometry.lerp (C.vertex (k + 1)) (C.vertex k) t ∈ C.set :=
  ⟨k, hk, by rw [C.chainEdge_eq, Geometry.segment_comm]; exact Geometry.lerp_mem_segment _ _ h0 h1⟩

theorem abs_snd_lt_radius (C : Chain) {p : Point} (hp : p ∈ C.set) : |p.2| < C.radius :=
  lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hp).2 C.coordBound_lt_radius

variable (J : Merge.Junction)

theorem sharedV_left : sharedV J = J.left.vertex J.m₁ := rfl

theorem sharedU_left : sharedU J = J.left.vertex (J.m₁ - 1 + 1 - 1) := by
  rw [show J.m₁ - 1 + 1 - 1 = J.m₁ - 1 by omega]; rfl

theorem sharedV_right : sharedV J = J.right.vertex 0 := by
  unfold sharedV; rw [← Merge.Junction.whole_vertex_add, Nat.add_zero]

theorem sharedW_right : sharedW J = J.right.vertex 1 := by
  unfold sharedW; rw [Merge.Junction.whole_vertex_add]

/-- The ratio of the nearer arm to the far arm is in `(0, 1)`. -/
theorem ratio_mem {a b : ℝ} (hab : 0 < a * b) (hle : |b| ≤ |a|) (hne : a ≠ b) :
    0 ≤ b / a ∧ b / a < 1 := by
  rcases lt_or_gt_of_ne (show a ≠ 0 by rintro rfl; simp at hab) with ha | ha
  · have hb : b < 0 := by
      by_contra h; push Not at h; nlinarith
    rw [abs_of_neg ha, abs_of_neg hb] at hle
    refine ⟨le_of_lt (div_pos_of_neg_of_neg hb ha), ?_⟩
    rw [div_lt_one_of_neg ha]
    rcases lt_or_gt_of_ne hne with h' | h' <;> linarith
  · have hb : 0 < b := by
      by_contra h; push Not at h; nlinarith
    rw [abs_of_pos ha, abs_of_pos hb] at hle
    refine ⟨le_of_lt (div_pos hb ha), ?_⟩
    rw [div_lt_one ha]
    rcases lt_or_gt_of_ne hne with h' | h' <;> linarith

/-- **The cap query on `C₁`** (the nearer arm is `w`, the far arm `[v, u]` is on `C₁`). -/
theorem capPos₀ (Q : Polygon) (hgen : SharedGeneric J) (hx : SharedExtremum J) (hu : ¬ NearU J)
    {h : ℕ} (hh : (Q.vtx h).2 = (capNear J).2) :
    (chainModel J.left).pos Q ⟨6 + tpos J.left J.m₁, h + 1⟩ = capOrigin J ∧
      0 ≤ (chainModel J.left).param Q ⟨6 + tpos J.left J.m₁, h + 1⟩ ∧
      (chainModel J.left).param Q ⟨6 + tpos J.left J.m₁, h + 1⟩ < 1 ∧
      capOrigin J ∈ J.left.set := by
  obtain ⟨g1, g2, g3⟩ := hgen
  have hnear : capNear J = sharedW J := by unfold capNear; exact ite_eq_right hu
  have hfar : capFar J = sharedU J := by unfold capFar; exact ite_eq_right hu
  have hm := J.one_le_m₁
  set M := chainModel J.left
  have ha : M.W.vtx (6 + tpos J.left J.m₁) = sharedV J := walk_vtx_tpos J.left (by show J.m₁ ≤ J.m₁; exact le_rfl)
  have hb : M.W.vtx ((6 + tpos J.left J.m₁ + 1) % M.W.n) = sharedU J := by
    have := tpos_lt J.left J.m₁
    have hlm : J.left.m = J.m₁ := rfl
    rw [hlm] at this
    rw [Nat.mod_eq_of_lt (by rw [cm_n, hlm]; omega)]
    exact left_next J
  have hpos := pos_edge (Q := Q) (h := h) ha hb (Ne.symm g1)
  have hpar : M.param Q ⟨6 + tpos J.left J.m₁, h + 1⟩ =
      ((sharedW J).2 - (sharedV J).2) / ((sharedU J).2 - (sharedV J).2) := by
    unfold Model.param Model.wa Model.wb; simp only
    rw [ha, hb, ite_eq_right (Ne.symm g1), hh, hnear]
  have hr := ratio_mem (a := (sharedU J).2 - (sharedV J).2) (b := (sharedW J).2 - (sharedV J).2)
    hx (not_lt.1 hu) (fun h => g3 (by linarith))
  have hco : capOrigin J = Geometry.lerp (sharedV J) (sharedU J)
      (((sharedW J).2 - (sharedV J).2) / ((sharedU J).2 - (sharedV J).2)) := by
    unfold capOrigin; rw [hnear, hfar]
  refine ⟨by rw [hpos, hh, hnear, hco], by rw [hpar]; exact hr.1, by rw [hpar]; exact hr.2, ?_⟩
  rw [hco, sharedV_left, sharedU_left]
  have := lerp_mem_set' J.left (k := J.m₁ - 1) (by show J.m₁ - 1 < J.m₁; omega) hr.1 hr.2.le
  rw [show J.m₁ - 1 + 1 = J.m₁ by omega] at this ⊢; assumption

/-- **The cap query on `C₂`** (the nearer arm is `u`, the far arm `[v, w]` is on `C₂`). -/
theorem capPos₁ (Q : Polygon) (hgen : SharedGeneric J) (hx : SharedExtremum J) (hu : NearU J)
    {h : ℕ} (hh : (Q.vtx h).2 = (capNear J).2) :
    (chainModel J.right).pos Q ⟨6 + tpos J.right 0, h + 1⟩ = capOrigin J ∧
      0 ≤ (chainModel J.right).param Q ⟨6 + tpos J.right 0, h + 1⟩ ∧
      (chainModel J.right).param Q ⟨6 + tpos J.right 0, h + 1⟩ < 1 ∧
      capOrigin J ∈ J.right.set := by
  obtain ⟨g1, g2, g3⟩ := hgen
  have hnear : capNear J = sharedU J := by unfold capNear; exact ite_eq_left hu
  have hfar : capFar J = sharedW J := by unfold capFar; exact ite_eq_left hu
  have hm := J.one_le_m₂
  set M := chainModel J.right
  have ha : M.W.vtx (6 + tpos J.right 0) = sharedV J := by
    rw [sharedV_right]; exact walk_vtx_tpos J.right (Nat.zero_le _)
  have hb : M.W.vtx ((6 + tpos J.right 0 + 1) % M.W.n) = sharedW J := by
    have := tpos_lt J.right 0
    have hrm : J.right.m = J.m₂ := rfl
    rw [hrm] at this
    rw [Nat.mod_eq_of_lt (by rw [cm_n, hrm]; omega)]
    exact right_next J
  have hpos := pos_edge (Q := Q) (h := h) ha hb (Ne.symm g2)
  have hpar : M.param Q ⟨6 + tpos J.right 0, h + 1⟩ =
      ((sharedU J).2 - (sharedV J).2) / ((sharedW J).2 - (sharedV J).2) := by
    unfold Model.param Model.wa Model.wb; simp only
    rw [ha, hb, ite_eq_right (Ne.symm g2), hh, hnear]
  have hx' : 0 < ((sharedW J).2 - (sharedV J).2) * ((sharedU J).2 - (sharedV J).2) := by
    have := hx; unfold SharedExtremum at this; linarith [mul_comm ((sharedU J).2 - (sharedV J).2)
      ((sharedW J).2 - (sharedV J).2)]
  have hr := ratio_mem (a := (sharedW J).2 - (sharedV J).2) (b := (sharedU J).2 - (sharedV J).2)
    hx' (le_of_lt hu) (fun h => g3 (by linarith))
  have hco : capOrigin J = Geometry.lerp (sharedV J) (sharedW J)
      (((sharedU J).2 - (sharedV J).2) / ((sharedW J).2 - (sharedV J).2)) := by
    unfold capOrigin; rw [hnear, hfar]
  refine ⟨by rw [hpos, hh, hnear, hco], by rw [hpar]; exact hr.1, by rw [hpar]; exact hr.2, ?_⟩
  rw [hco, sharedV_right, sharedW_right]
  exact lerp_mem_set J.right (k := 0) (by show 0 < J.m₂; omega) hr.1 hr.2.le

/-- The cap direction from the direction bit of `capPrim`. -/
theorem capDir_eq {ρ : ℕ} (h : ρ ≤ 1 ∧ (ρ = 1 ↔ ¬ (capNear J).1 < (capOrigin J).1)) :
    dirOf ρ = capDir J := by
  unfold dirOf capDir
  by_cases hc : (capNear J).1 < (capOrigin J).1
  · rw [ite_eq_left hc, ite_eq_right (fun h1 => (h.2.1 h1) hc)]
  · rw [ite_eq_right hc, ite_eq_left (h.2.2 hc)]

end

end FuseAsm

end Chazelle.Core
