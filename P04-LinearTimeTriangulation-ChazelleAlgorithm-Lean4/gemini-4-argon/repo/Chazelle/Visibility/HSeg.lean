module

public import Chazelle.Visibility.Map

/-!
# The free horizontal segment through a free point

Let `q` be a *free* point of a simple polygon `P`: interior and on no vertex chord
(`q ∈ freeRegion P`).  The horizontal line through `q` meets the boundary first at
`leftEnd P q = (q.1 - leftHitParam P q, q.2)` and `rightEnd P q = (q.1 + rightHitParam P q, q.2)`
(see `Ray.lean`), and the open segment between them is `openHSeg P q`.  This file proves:

* `openHSeg_subset_interior`: the open segment is interior, and its closure meets the boundary
  only in the two endpoints (`closedHSeg_inter_boundary`);
* `rightEnd_ne_vtx`, `leftEnd_ne_vtx`: **the endpoints are not vertices** (a vertex there would
  emit a chord through `q`, see `rayPt_mem_chordUnion`), hence no vertex lies on the closed
  segment (`not_vtx_mem_closedHSeg`);
* `openHSeg_subset_freeRegion`: **the open segment is free** (a chord through one of its points
  would have an endpoint in the open segment);
* `exists_rightEdge`, `exists_leftEdge`: each endpoint lies on the open part of a unique edge,
  and that edge is not horizontal.

The file also sets up non-horizontal edges as graphs over the height: `xAt u w y` is the
abscissa of the line through `u, w` at height `y`, `edgeX P i`, `edgeBot P i`, `edgeTop P i`
describe edge `i`, and `mem_edge_iff_edgeX`, `openEdgePt_iff_edgeX` characterise membership.
-/

namespace Chazelle.Visibility

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one point_ext point_ext_iff
  lerp_mem_segment continuous_lerp)

/-! ### Lines as graphs over the height -/

/-- The abscissa of the point at height `y` on the line through `u` and `w` (meaningful when
`u.2 ≠ w.2`). -/
noncomputable def xAt (u w : Point) (y : ℝ) : ℝ := u.1 + (y - u.2) * ((w.1 - u.1) / (w.2 - u.2))

theorem xAt_left (u w : Point) : xAt u w u.2 = u.1 := by simp [xAt]

theorem xAt_right {u w : Point} (h : u.2 ≠ w.2) : xAt u w w.2 = w.1 := by
  have hne : w.2 - u.2 ≠ 0 := sub_ne_zero.2 h.symm
  unfold xAt
  field_simp
  ring

theorem xAt_lerp {u w : Point} (h : u.2 ≠ w.2) (t : ℝ) :
    xAt u w (lerp u w t).2 = (lerp u w t).1 := by
  have hne : w.2 - u.2 ≠ 0 := sub_ne_zero.2 h.symm
  unfold xAt
  simp only [lerp_fst, lerp_snd]
  field_simp
  ring

/-- `xAt u w` is affine. -/
theorem xAt_combo (u w : Point) {s t : ℝ} (hst : s + t = 1) (y y' : ℝ) :
    xAt u w (s * y + t * y') = s * xAt u w y + t * xAt u w y' := by
  unfold xAt
  have : t = 1 - s := by linarith
  subst this
  ring

theorem continuous_xAt (u w : Point) : Continuous (xAt u w) := by
  unfold xAt; fun_prop

/-- Membership in a non-horizontal segment: the height is between the endpoint heights and the
abscissa is the one of the line. -/
theorem mem_segment_iff_xAt {u w : Point} (h : u.2 ≠ w.2) {p : Point} :
    p ∈ Chazelle.segment u w ↔
      (min u.2 w.2 ≤ p.2 ∧ p.2 ≤ max u.2 w.2) ∧ p.1 = xAt u w p.2 := by
  have hne : w.2 - u.2 ≠ 0 := sub_ne_zero.2 h.symm
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · dsimp only
      rcases lt_or_gt_of_ne h with hlt | hgt
      · rw [min_eq_left hlt.le]; nlinarith
      · rw [min_eq_right hgt.le]; nlinarith
    · dsimp only
      rcases lt_or_gt_of_ne h with hlt | hgt
      · rw [max_eq_right hlt.le]; nlinarith
      · rw [max_eq_left hgt.le]; nlinarith
    · exact (xAt_lerp h t).symm
  · rintro ⟨⟨h1, h2⟩, hx⟩
    refine ⟨(p.2 - u.2) / (w.2 - u.2), ?_, ?_, ?_⟩
    · rcases lt_or_gt_of_ne h with hlt | hgt
      · rw [min_eq_left hlt.le] at h1
        exact div_nonneg (by linarith) (by linarith)
      · rw [max_eq_left hgt.le] at h2
        exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · rcases lt_or_gt_of_ne h with hlt | hgt
      · rw [max_eq_right hlt.le] at h2
        rw [div_le_one (by linarith)]; linarith
      · rw [min_eq_right hgt.le] at h1
        rw [div_le_one_of_neg (by linarith)]; linarith
    · rw [point_ext_iff]
      dsimp only
      constructor
      · rw [hx]; unfold xAt; ring
      · rw [div_mul_cancel₀ _ hne]; ring

/-- Membership in the open part of a non-horizontal segment. -/
theorem openSegment_iff_xAt {u w : Point} (h : u.2 ≠ w.2) {p : Point} :
    (∃ t ∈ Ioo (0 : ℝ) 1, p = lerp u w t) ↔
      (min u.2 w.2 < p.2 ∧ p.2 < max u.2 w.2) ∧ p.1 = xAt u w p.2 := by
  have hne : w.2 - u.2 ≠ 0 := sub_ne_zero.2 h.symm
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, (xAt_lerp h t).symm⟩
    · simp only [lerp_snd]
      rcases lt_or_gt_of_ne h with hlt | hgt
      · rw [min_eq_left hlt.le]; nlinarith
      · rw [min_eq_right hgt.le]; nlinarith
    · simp only [lerp_snd]
      rcases lt_or_gt_of_ne h with hlt | hgt
      · rw [max_eq_right hlt.le]; nlinarith
      · rw [max_eq_left hgt.le]; nlinarith
  · rintro ⟨⟨h1, h2⟩, hx⟩
    refine ⟨(p.2 - u.2) / (w.2 - u.2), ⟨?_, ?_⟩, ?_⟩
    · rcases lt_or_gt_of_ne h with hlt | hgt
      · rw [min_eq_left hlt.le] at h1
        exact div_pos (by linarith) (by linarith)
      · rw [max_eq_left hgt.le] at h2
        exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    · rcases lt_or_gt_of_ne h with hlt | hgt
      · rw [max_eq_right hlt.le] at h2
        rw [div_lt_one (by linarith)]; linarith
      · rw [min_eq_right hgt.le] at h1
        rw [div_lt_one_of_neg (by linarith)]; linarith
    · rw [point_ext_iff]
      simp only [lerp_fst, lerp_snd]
      constructor
      · rw [hx]; unfold xAt; ring
      · rw [div_mul_cancel₀ _ hne]; ring

/-! ### Edges of a polygon as graphs -/

/-- The abscissa of edge `i` (extended to a line) at height `y`. -/
noncomputable def edgeX (P : Polygon) (i : ℕ) (y : ℝ) : ℝ := xAt (P.vtx i) (P.vtx ((i + 1) % P.n)) y

/-- The lower height of edge `i`. -/
def edgeBot (P : Polygon) (i : ℕ) : ℝ := min (P.vtx i).2 (P.vtx ((i + 1) % P.n)).2

/-- The upper height of edge `i`. -/
def edgeTop (P : Polygon) (i : ℕ) : ℝ := max (P.vtx i).2 (P.vtx ((i + 1) % P.n)).2

/-- Edge `i` is not horizontal. -/
def NonHoriz (P : Polygon) (i : ℕ) : Prop := (P.vtx i).2 ≠ (P.vtx ((i + 1) % P.n)).2

/-- `p` lies on the open part of edge `i`. -/
def OpenEdgePt (P : Polygon) (i : ℕ) (p : Point) : Prop :=
  ∃ t ∈ Ioo (0 : ℝ) 1, p = lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t

theorem continuous_edgeX (P : Polygon) (i : ℕ) : Continuous (edgeX P i) := continuous_xAt _ _

theorem edgeX_combo (P : Polygon) (i : ℕ) {s t : ℝ} (hst : s + t = 1) (y y' : ℝ) :
    edgeX P i (s * y + t * y') = s * edgeX P i y + t * edgeX P i y' :=
  xAt_combo _ _ hst y y'

/-- Membership in a non-horizontal edge. -/
theorem mem_edge_iff_edgeX {P : Polygon} {i : ℕ} (h : NonHoriz P i) {p : Point} :
    p ∈ P.edge i ↔ (edgeBot P i ≤ p.2 ∧ p.2 ≤ edgeTop P i) ∧ p.1 = edgeX P i p.2 :=
  mem_segment_iff_xAt h

/-- Membership in the open part of a non-horizontal edge. -/
theorem openEdgePt_iff_edgeX {P : Polygon} {i : ℕ} (h : NonHoriz P i) {p : Point} :
    OpenEdgePt P i p ↔ (edgeBot P i < p.2 ∧ p.2 < edgeTop P i) ∧ p.1 = edgeX P i p.2 :=
  openSegment_iff_xAt h

theorem OpenEdgePt.mem_edge {P : Polygon} {i : ℕ} {p : Point} (h : OpenEdgePt P i p) :
    p ∈ P.edge i := by
  obtain ⟨t, ht, rfl⟩ := h
  exact lerp_mem_segment _ _ ht.1.le ht.2.le

theorem OpenEdgePt.mem_boundary {P : Polygon} {i : ℕ} (hi : i < P.n) {p : Point}
    (h : OpenEdgePt P i p) : p ∈ P.boundary :=
  ⟨i, hi, h.mem_edge⟩

/-- A point of the open part of edge `i` lies on no other edge. -/
theorem OpenEdgePt.not_mem_other {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {p : Point}
    (h : OpenEdgePt P i p) {k : ℕ} (hk : k < P.n) (hki : k ≠ i) : p ∉ P.edge k := by
  obtain ⟨t, ht, rfl⟩ := h
  exact simple_openEdge_not_mem_other hP hi ht hk hki

/-- A point of the open part of an edge is not a vertex. -/
theorem OpenEdgePt.ne_vtx {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {p : Point}
    (h : OpenEdgePt P i p) {k : ℕ} (hk : k < P.n) : p ≠ P.vtx k := by
  obtain ⟨t, ht, rfl⟩ := h
  exact simple_openEdge_ne_vtx hP hi ht hk

/-- The top endpoint of a non-horizontal edge is a vertex on the line of the edge. -/
theorem exists_vtx_edgeTop {P : Polygon} {i : ℕ} (hi : i < P.n) (h : NonHoriz P i) :
    ∃ k, k < P.n ∧ (P.vtx k).2 = edgeTop P i ∧ (P.vtx k).1 = edgeX P i (edgeTop P i) := by
  unfold edgeTop edgeX
  rcases lt_or_gt_of_ne h with hlt | hgt
  · refine ⟨(i + 1) % P.n, succIdx_lt P hi, ?_, ?_⟩
    · rw [max_eq_right hlt.le]
    · rw [max_eq_right hlt.le, xAt_right h]
  · refine ⟨i, hi, ?_, ?_⟩
    · rw [max_eq_left hgt.le]
    · rw [max_eq_left hgt.le, xAt_left]

/-- The bottom endpoint of a non-horizontal edge is a vertex on the line of the edge. -/
theorem exists_vtx_edgeBot {P : Polygon} {i : ℕ} (hi : i < P.n) (h : NonHoriz P i) :
    ∃ k, k < P.n ∧ (P.vtx k).2 = edgeBot P i ∧ (P.vtx k).1 = edgeX P i (edgeBot P i) := by
  unfold edgeBot edgeX
  rcases lt_or_gt_of_ne h with hlt | hgt
  · refine ⟨i, hi, ?_, ?_⟩
    · rw [min_eq_left hlt.le]
    · rw [min_eq_left hlt.le, xAt_left]
  · refine ⟨(i + 1) % P.n, succIdx_lt P hi, ?_, ?_⟩
    · rw [min_eq_right hgt.le]
    · rw [min_eq_right hgt.le, xAt_right h]

/-! ### The horizontal segment of a free point -/

/-- The first boundary point to the left of `q` on its horizontal line. -/
noncomputable def leftEnd (P : Polygon) (q : Point) : Point := (q.1 - leftHitParam P q, q.2)

/-- The first boundary point to the right of `q` on its horizontal line. -/
noncomputable def rightEnd (P : Polygon) (q : Point) : Point := (q.1 + rightHitParam P q, q.2)

@[simp] theorem leftEnd_fst (P : Polygon) (q : Point) : (leftEnd P q).1 = q.1 - leftHitParam P q :=
  rfl
@[simp] theorem leftEnd_snd (P : Polygon) (q : Point) : (leftEnd P q).2 = q.2 := rfl
@[simp] theorem rightEnd_fst (P : Polygon) (q : Point) :
    (rightEnd P q).1 = q.1 + rightHitParam P q := rfl
@[simp] theorem rightEnd_snd (P : Polygon) (q : Point) : (rightEnd P q).2 = q.2 := rfl

theorem leftEnd_fst_lt {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ P.filled \ P.boundary) :
    (leftEnd P q).1 < q.1 := by
  rw [leftEnd_fst]; linarith [leftHitParam_pos hP hq]

theorem lt_rightEnd_fst {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ P.filled \ P.boundary) :
    q.1 < (rightEnd P q).1 := by
  rw [rightEnd_fst]; linarith [rightHitParam_pos hP hq]

theorem leftEnd_mem_boundary {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) : leftEnd P q ∈ P.boundary :=
  leftHit_mem_boundary hP hq

theorem rightEnd_mem_boundary {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) : rightEnd P q ∈ P.boundary :=
  rightHit_mem_boundary hP hq

/-- A point of the horizontal line through `q` strictly between the two first hits is interior. -/
theorem mem_interior_of_between {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) {p : Point} (hy : p.2 = q.2) (h1 : (leftEnd P q).1 < p.1)
    (h2 : p.1 < (rightEnd P q).1) : p ∈ P.filled \ P.boundary := by
  rw [leftEnd_fst] at h1
  rw [rightEnd_fst] at h2
  rcases le_or_gt q.1 p.1 with h | h
  · have := open_ray_subset_interior hP hq (p.1 - q.1) (by linarith) (by linarith)
    rwa [show (q.1 + (p.1 - q.1), q.2) = p from point_ext (by ring) hy.symm] at this
  · have := open_left_ray_subset_interior hP hq (q.1 - p.1) (by linarith) (by linarith)
    rwa [show (q.1 - (q.1 - p.1), q.2) = p from point_ext (by ring) hy.symm] at this

/-- The closed horizontal segment meets the boundary only in its two endpoints. -/
theorem closedHSeg_inter_boundary {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) {p : Point} (hy : p.2 = q.2) (h1 : (leftEnd P q).1 ≤ p.1)
    (h2 : p.1 ≤ (rightEnd P q).1) (hp : p ∈ P.boundary) : p = leftEnd P q ∨ p = rightEnd P q := by
  rcases h1.lt_or_eq with h1 | h1
  · rcases h2.lt_or_eq with h2 | h2
    · exact absurd hp (mem_interior_of_between hP hq hy h1 h2).2
    · exact Or.inr (point_ext h2 hy)
  · exact Or.inl (point_ext h1.symm hy)

/-! ### Chords emitted towards interior points -/

/-- If the open horizontal stretch from vertex `i` in direction `σ` up to parameter `s` is
interior, the point at parameter `s` lies on the chord of `i` in direction `σ`. -/
theorem rayPt_mem_chordUnion {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {s : ℝ} (hs : 0 < s)
    (hint : ∀ t, 0 < t → t < s → rayPt (P.vtx i) σ t ∈ P.filled \ P.boundary) :
    rayPt (P.vtx i) σ s ∈ chordUnion P := by
  have hdir : DirInterior P i σ := by
    unfold DirInterior
    filter_upwards [Ioo_mem_nhdsGT hs] with t ht
    exact hint t ht.1 ht.2
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hle : s ≤ chordParam P i σ := (hit_of_initial hP hσ0 hs hint).1
  refine ⟨chordSet P i σ, ⟨i, σ, hi, hσ, hdir, rfl⟩, ?_⟩
  rw [chordSet_eq_image hP hi hdir]
  exact ⟨s, ⟨hs.le, hle⟩, rfl⟩

/-- **The right endpoint of the horizontal segment of a free point is not a vertex.** -/
theorem rightEnd_ne_vtx {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ freeRegion P) {k : ℕ}
    (hk : k < P.n) : rightEnd P q ≠ P.vtx k := by
  intro heq
  have hq' : q ∈ P.filled \ P.boundary := hq.1
  have hR := rightHitParam_pos hP hq'
  apply hq.2
  have e : ∀ t, rayPt (P.vtx k) (-1) t = (q.1 + (rightHitParam P q - t), q.2) := by
    intro t
    rw [← heq]
    exact point_ext (by simp [rayPt]; ring) (by simp [rayPt])
  have hmem := rayPt_mem_chordUnion hP hk (Or.inr rfl) hR (fun t ht1 ht2 => by
    rw [e]
    exact open_ray_subset_interior hP hq' _ (by linarith) (by linarith))
  rwa [e, sub_self, add_zero] at hmem

/-- **The left endpoint of the horizontal segment of a free point is not a vertex.** -/
theorem leftEnd_ne_vtx {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ freeRegion P) {k : ℕ}
    (hk : k < P.n) : leftEnd P q ≠ P.vtx k := by
  intro heq
  have hq' : q ∈ P.filled \ P.boundary := hq.1
  have hL := leftHitParam_pos hP hq'
  apply hq.2
  have e : ∀ t, rayPt (P.vtx k) 1 t = (q.1 - (leftHitParam P q - t), q.2) := by
    intro t
    rw [← heq]
    exact point_ext (by simp [rayPt]; ring) (by simp [rayPt])
  have hmem := rayPt_mem_chordUnion hP hk (Or.inl rfl) hL (fun t ht1 ht2 => by
    rw [e]
    exact open_left_ray_subset_interior hP hq' _ (by linarith) (by linarith))
  rwa [e, sub_self, sub_zero] at hmem

/-- **No vertex on the closed horizontal segment of a free point.** -/
theorem not_vtx_mem_closedHSeg {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ freeRegion P)
    {k : ℕ} (hk : k < P.n) (hy : (P.vtx k).2 = q.2) (h1 : (leftEnd P q).1 ≤ (P.vtx k).1)
    (h2 : (P.vtx k).1 ≤ (rightEnd P q).1) : False := by
  have hb : P.vtx k ∈ P.boundary := ⟨k, hk, Geometry.left_mem_segment _ _⟩
  rcases closedHSeg_inter_boundary hP hq.1 hy h1 h2 hb with h | h
  · exact leftEnd_ne_vtx hP hq hk h.symm
  · exact rightEnd_ne_vtx hP hq hk h.symm

/-! ### The endpoints lie on open non-horizontal edges -/

/-- A horizontal edge at the height of an interior point `q` cannot contain, in its open part,
a first hit of the horizontal ray from `q`: it would contain `q` or an interior point. -/
theorem nonHoriz_of_openEdgePt_end {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) {j : ℕ} (hj : j < P.n) {p : Point} (hp : OpenEdgePt P j p)
    (hpy : p.2 = q.2) (h1 : (leftEnd P q).1 ≤ p.1) (h2 : p.1 ≤ (rightEnd P q).1) :
    NonHoriz P j := by
  intro hh
  set u := P.vtx j
  set w := P.vtx ((j + 1) % P.n)
  obtain ⟨t, ht, hpt⟩ := hp
  have huw : u ≠ w := simple_vtx_succ_ne hP hj
  have huw1 : u.1 ≠ w.1 := fun h => huw (point_ext h hh)
  have hedge : P.edge j = hseg u.2 (min u.1 w.1) (max u.1 w.1) := segment_horizontal_eq_hseg hh
  have hpu : p.2 = u.2 := by rw [hpt, lerp_snd, ← hh]; ring
  have hqu : q.2 = u.2 := hpy.symm.trans hpu
  -- the abscissa of `p` is strictly between the endpoint abscissae
  have hp1 : p.1 = u.1 + t * (w.1 - u.1) := by rw [hpt, lerp_fst]
  have hmin : min u.1 w.1 < p.1 := by
    rcases lt_or_gt_of_ne huw1 with h | h
    · rw [min_eq_left h.le, hp1]; nlinarith [ht.1, ht.2]
    · rw [min_eq_right h.le, hp1]; nlinarith [ht.1, ht.2]
  have hmax : p.1 < max u.1 w.1 := by
    rcases lt_or_gt_of_ne huw1 with h | h
    · rw [max_eq_right h.le, hp1]; nlinarith [ht.1, ht.2]
    · rw [max_eq_left h.le, hp1]; nlinarith [ht.1, ht.2]
  rw [leftEnd_fst] at h1
  rw [rightEnd_fst] at h2
  by_cases hmq : min u.1 w.1 ≤ q.1
  · by_cases hqM : q.1 ≤ max u.1 w.1
    · exact hq.2 ⟨j, hj, by rw [hedge]; exact ⟨hqu, hmq, hqM⟩⟩
    · -- `q` is to the right of the edge, so `max` lies strictly inside the left ray
      have hint := open_left_ray_subset_interior hP hq (q.1 - max u.1 w.1) (by linarith)
        (by linarith)
      apply hint.2
      refine ⟨j, hj, ?_⟩
      rw [hedge]
      exact ⟨hqu, by dsimp only; linarith [min_le_max (a := u.1) (b := w.1)], by dsimp only; linarith⟩
  · have hint := open_ray_subset_interior hP hq (min u.1 w.1 - q.1) (by linarith) (by linarith)
    apply hint.2
    refine ⟨j, hj, ?_⟩
    rw [hedge]
    exact ⟨hqu, by dsimp only; linarith, by dsimp only; linarith [min_le_max (a := u.1) (b := w.1)]⟩

/-- **The right endpoint lies on the open part of a non-horizontal edge.** -/
theorem exists_rightEdge {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ freeRegion P) :
    ∃ j, j < P.n ∧ OpenEdgePt P j (rightEnd P q) ∧ NonHoriz P j := by
  obtain ⟨j, hj, t, ht, heq⟩ := exists_openEdge_of_mem_boundary P (rightEnd_mem_boundary hP hq.1)
    (fun k hk => rightEnd_ne_vtx hP hq hk)
  have hop : OpenEdgePt P j (rightEnd P q) := ⟨t, ht, heq⟩
  exact ⟨j, hj, hop, nonHoriz_of_openEdgePt_end hP hq.1 hj hop rfl
    (by rw [leftEnd_fst, rightEnd_fst]; linarith [leftHitParam_pos hP hq.1, rightHitParam_pos hP hq.1])
    le_rfl⟩

/-- **The left endpoint lies on the open part of a non-horizontal edge.** -/
theorem exists_leftEdge {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ freeRegion P) :
    ∃ i, i < P.n ∧ OpenEdgePt P i (leftEnd P q) ∧ NonHoriz P i := by
  obtain ⟨i, hi, t, ht, heq⟩ := exists_openEdge_of_mem_boundary P (leftEnd_mem_boundary hP hq.1)
    (fun k hk => leftEnd_ne_vtx hP hq hk)
  have hop : OpenEdgePt P i (leftEnd P q) := ⟨t, ht, heq⟩
  exact ⟨i, hi, hop, nonHoriz_of_openEdgePt_end hP hq.1 hi hop rfl le_rfl
    (by rw [leftEnd_fst, rightEnd_fst]; linarith [leftHitParam_pos hP hq.1, rightHitParam_pos hP hq.1])⟩

/-- The abscissa of the right endpoint is the one of its edge at height `q.2`. -/
theorem rightEnd_fst_eq_edgeX {P : Polygon} {q : Point} {j : ℕ} (hj : NonHoriz P j)
    (h : OpenEdgePt P j (rightEnd P q)) : (rightEnd P q).1 = edgeX P j q.2 := by
  have := ((openEdgePt_iff_edgeX hj).1 h).2
  rwa [rightEnd_snd] at this

/-- The abscissa of the left endpoint is the one of its edge at height `q.2`. -/
theorem leftEnd_fst_eq_edgeX {P : Polygon} {q : Point} {i : ℕ} (hi : NonHoriz P i)
    (h : OpenEdgePt P i (leftEnd P q)) : (leftEnd P q).1 = edgeX P i q.2 := by
  have := ((openEdgePt_iff_edgeX hi).1 h).2
  rwa [leftEnd_snd] at this

/-- The two edges carrying the endpoints are distinct. -/
theorem leftEdge_ne_rightEdge {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) {i j : ℕ} (hi : NonHoriz P i) (hj : NonHoriz P j)
    (hL : OpenEdgePt P i (leftEnd P q)) (hR : OpenEdgePt P j (rightEnd P q)) : i ≠ j := by
  rintro rfl
  have h1 := leftEnd_fst_eq_edgeX hi hL
  have h2 := rightEnd_fst_eq_edgeX hj hR
  have := leftEnd_fst_lt hP hq
  have := lt_rightEnd_fst hP hq
  linarith

end

end Chazelle.Visibility
