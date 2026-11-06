module

public meta import Chazelle.Arithmetic

public import Chazelle.Visibility.HSeg

/-!
# Every region of the horizontal visibility map is an open trapezoid

Let `q` be a free point of a simple polygon `P` (`q ∈ freeRegion P`, see `Map.lean`), and let
`i`, `j` be the (non-horizontal) edges carrying the two endpoints `leftEnd P q`, `rightEnd P q`
of its horizontal segment (`HSeg.lean`).  The lines of these edges are the graphs
`x = edgeX P i y` and `x = edgeX P j y`.  The *corridor* between them is obstructed above `q`
at the first height `y₂ > q.2` where an endpoint of `i` or `j`, or a vertex lying in the closed
corridor, occurs; similarly `y₁ < q.2` below.  The structure `IsTrap P q i j y₁ y₂` records this
choice, and

  `trapSet P i j y₁ y₂ = {p | y₁ < p.2 < y₂ ∧ edgeX P i p.2 < p.1 < edgeX P j p.2}`

is the open trapezoid.  Main results:

* `exists_isTrap`: every free point has such data;
* `IsTrap.trapSet_subset_freeRegion`: the trapezoid is free (no boundary point: an edge meeting
  it would reach the horizontal segment of `q` or leave through a side, `segment_exit`; no chord
  point: the emitting vertex is outside the corridor, so the chord would cross a side);
* `IsTrap.closure_inter_free`: a free point of the closure of the trapezoid is in the trapezoid
  (the open top and bottom sides contain no free point, `not_free_of_side`);
* `IsTrap.region_eq`: **the region of `q` is exactly the trapezoid**;
* `regions_eq_trapSet`, `regions_convex`: every region of the visibility map is an open
  trapezoid, in particular convex;
* `IsTrap.top_side`, `IsTrap.bot_side`: the open top and bottom sides consist of boundary points
  and chord points.
-/

namespace Chazelle.Visibility

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one point_ext point_ext_iff
  lerp_mem_segment continuous_lerp)

/-! ### The trapezoid -/

section
variable (P : Polygon) (i j : ℕ) (y₁ y₂ : ℝ)
include P i j y₁ y₂
/-- The open trapezoid between heights `y₁` and `y₂`, bounded on the left by the line of edge
`i` and on the right by the line of edge `j`. -/
def trapSet : Set Point :=
  {p | y₁ < p.2 ∧ p.2 < y₂ ∧ edgeX P i p.2 < p.1 ∧ p.1 < edgeX P j p.2}

/-- The closed trapezoid. -/
def closedTrap : Set Point :=
  {p | y₁ ≤ p.2 ∧ p.2 ≤ y₂ ∧ edgeX P i p.2 ≤ p.1 ∧ p.1 ≤ edgeX P j p.2}


end

section
variable (P : Polygon) (i j : ℕ) (y₁ y₂ : ℝ)
theorem isOpen_trapSet : IsOpen (trapSet P i j y₁ y₂) := by
  have h1 : IsOpen {p : Point | y₁ < p.2} := isOpen_lt continuous_const continuous_snd
  have h2 : IsOpen {p : Point | p.2 < y₂} := isOpen_lt continuous_snd continuous_const
  have h3 : IsOpen {p : Point | edgeX P i p.2 < p.1} :=
    isOpen_lt ((continuous_edgeX P i).comp continuous_snd) continuous_fst
  have h4 : IsOpen {p : Point | p.1 < edgeX P j p.2} :=
    isOpen_lt continuous_fst ((continuous_edgeX P j).comp continuous_snd)
  have : trapSet P i j y₁ y₂ = {p : Point | y₁ < p.2} ∩ ({p : Point | p.2 < y₂} ∩
      ({p : Point | edgeX P i p.2 < p.1} ∩ {p : Point | p.1 < edgeX P j p.2})) := by
    aesop
  rw [this]
  exact h1.inter (h2.inter (h3.inter h4))

theorem isClosed_closedTrap :
    IsClosed (closedTrap P i j y₁ y₂) := by
  have h1 : IsClosed {p : Point | y₁ ≤ p.2} := isClosed_le continuous_const continuous_snd
  have h2 : IsClosed {p : Point | p.2 ≤ y₂} := isClosed_le continuous_snd continuous_const
  have h3 : IsClosed {p : Point | edgeX P i p.2 ≤ p.1} :=
    isClosed_le ((continuous_edgeX P i).comp continuous_snd) continuous_fst
  have h4 : IsClosed {p : Point | p.1 ≤ edgeX P j p.2} :=
    isClosed_le continuous_fst ((continuous_edgeX P j).comp continuous_snd)
  have : closedTrap P i j y₁ y₂ = {p : Point | y₁ ≤ p.2} ∩ ({p : Point | p.2 ≤ y₂} ∩
      ({p : Point | edgeX P i p.2 ≤ p.1} ∩ {p : Point | p.1 ≤ edgeX P j p.2})) := by
    aesop
  rw [this]
  exact h1.inter (h2.inter (h3.inter h4))

theorem trapSet_subset_closedTrap :
    trapSet P i j y₁ y₂ ⊆ closedTrap P i j y₁ y₂ :=
  fun _ hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.le⟩

theorem closure_trapSet_subset :
    closure (trapSet P i j y₁ y₂) ⊆ closedTrap P i j y₁ y₂ :=
  closure_minimal (trapSet_subset_closedTrap P i j y₁ y₂) (isClosed_closedTrap P i j y₁ y₂)


end

/-- Strict inequalities are preserved by convex combinations. -/
theorem combo_lt_combo {a b a' b' s s' : ℝ} (h1 : a < a') (h2 : b < b') (hs : 0 ≤ s)
    (hs' : 0 ≤ s') (h : s + s' = 1) : s * a + s' * b < s * a' + s' * b' := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · simp_all
  nlinarith

/-- The open trapezoid is convex. -/
theorem convex_trapSet (P : Polygon) (i j : ℕ) (y₁ y₂ : ℝ) : Convex ℝ (trapSet P i j y₁ y₂) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · show y₁ < (a • x + b • y).2
    simp only [Geometry.add_snd, Geometry.smul_snd]
    exact combo_lt hx1 hy1 ha hb hab
  · show (a • x + b • y).2 < y₂
    simp only [Geometry.add_snd, Geometry.smul_snd]
    exact combo_gt hx2 hy2 ha hb hab
  · show edgeX P i (a • x + b • y).2 < (a • x + b • y).1
    simp only [Geometry.add_snd, Geometry.smul_snd, Geometry.add_fst, Geometry.smul_fst]
    rw [edgeX_combo P i hab]
    exact combo_lt_combo hx3 hy3 ha hb hab
  · show (a • x + b • y).1 < edgeX P j (a • x + b • y).2
    simp only [Geometry.add_snd, Geometry.smul_snd, Geometry.add_fst, Geometry.smul_fst]
    rw [edgeX_combo P j hab]
    exact combo_lt_combo hx4 hy4 ha hb hab

/-- A preconnected set avoiding the boundary and containing an interior point is interior. -/
theorem subset_interior_of_isPreconnected {P : Polygon} (hP : P.Simple) {S : Set Point}
    (hS : IsPreconnected S) (hSb : ∀ p ∈ S, p ∉ P.boundary) {z : Point} (hz : z ∈ S)
    (hzi : z ∈ P.filled \ P.boundary) : S ⊆ P.filled \ P.boundary := by
  intro p hp
  refine ⟨?_, hSb p hp⟩
  rw [mem_filled_iff hP (hSb p hp), parity_eq_of_isPreconnected P hS (fun x hx => hSb x hx) hp hz,
    ← mem_filled_iff hP hzi.2]
  exact hzi.1

/-! ### The trapezoid data of a free point -/

/-- The data describing the region of a free point `q`: the two non-horizontal edges `i`
(left) and `j` (right) carrying the endpoints of its horizontal segment, and the heights
`y₁ < q.2 < y₂` of the bottom and top sides.  The heights stay within the ranges of both edges,
no vertex lies in the closed corridor strictly between the heights, and each height carries a
vertex of the closed corridor (or an endpoint of `i` or `j`). -/
structure IsTrap (P : Polygon) (q : Point) (i j : ℕ) (y₁ y₂ : ℝ) : Prop where
  hi : i < P.n
  hj : j < P.n
  nhL : NonHoriz P i
  nhR : NonHoriz P j
  left_mem : OpenEdgePt P i (leftEnd P q)
  right_mem : OpenEdgePt P j (rightEnd P q)
  bot_lt : y₁ < q.2
  lt_top : q.2 < y₂
  botL : edgeBot P i ≤ y₁
  botR : edgeBot P j ≤ y₁
  topL : y₂ ≤ edgeTop P i
  topR : y₂ ≤ edgeTop P j
  no_vertex : ∀ k, k < P.n → y₁ < (P.vtx k).2 → (P.vtx k).2 < y₂ →
    edgeX P i (P.vtx k).2 ≤ (P.vtx k).1 → (P.vtx k).1 ≤ edgeX P j (P.vtx k).2 → False
  top_vertex : ∃ k, k < P.n ∧ (P.vtx k).2 = y₂ ∧
    (edgeX P i y₂ ≤ edgeX P j y₂ → edgeX P i y₂ ≤ (P.vtx k).1 ∧ (P.vtx k).1 ≤ edgeX P j y₂)
  bot_vertex : ∃ k, k < P.n ∧ (P.vtx k).2 = y₁ ∧
    (edgeX P i y₁ ≤ edgeX P j y₁ → edgeX P i y₁ ≤ (P.vtx k).1 ∧ (P.vtx k).1 ≤ edgeX P j y₁)

namespace IsTrap

variable {P : Polygon} {q : Point} {i j : ℕ} {y₁ y₂ : ℝ}

section
variable (h : IsTrap P q i j y₁ y₂)
include h
theorem leftEnd_eq : (leftEnd P q).1 = edgeX P i q.2 :=
  leftEnd_fst_eq_edgeX h.nhL h.left_mem

theorem rightEnd_eq : (rightEnd P q).1 = edgeX P j q.2 :=
  rightEnd_fst_eq_edgeX h.nhR h.right_mem


end

theorem ne (hP : P.Simple) (hq : q ∈ P.filled \ P.boundary) (h : IsTrap P q i j y₁ y₂) : i ≠ j :=
  leftEdge_ne_rightEdge hP hq h.nhL h.nhR h.left_mem h.right_mem

section
variable (h : IsTrap P q i j y₁ y₂) {p : Point} (h1 : y₁ ≤ p.2) (h2 : p.2 ≤ y₂)
include h h1 h2
/-- A point on the line of edge `i` at a height of the trapezoid's range lies on edge `i`. -/
theorem mem_edgeL
    (hx : p.1 = edgeX P i p.2) : p ∈ P.edge i :=
  (mem_edge_iff_edgeX h.nhL).2 ⟨⟨h.botL.trans h1, h2.trans h.topL⟩, hx⟩

/-- A point on the line of edge `j` at a height of the trapezoid's range lies on edge `j`. -/
theorem mem_edgeR
    (hx : p.1 = edgeX P j p.2) : p ∈ P.edge j :=
  (mem_edge_iff_edgeX h.nhR).2 ⟨⟨h.botR.trans h1, h2.trans h.topR⟩, hx⟩


end

theorem q_mem (hP : P.Simple) (hq : q ∈ P.filled \ P.boundary) (h : IsTrap P q i j y₁ y₂) :
    q ∈ trapSet P i j y₁ y₂ :=
  ⟨h.bot_lt, h.lt_top, by rw [← h.leftEnd_eq]; exact leftEnd_fst_lt hP hq,
    by rw [← h.rightEnd_eq]; exact lt_rightEnd_fst hP hq⟩

end IsTrap

/-! ### Existence of the trapezoid data -/

section
variable {P : Polygon} {q : Point} {i j : ℕ} (hi : i < P.n) (hj : j < P.n) (nhL : NonHoriz P i) (nhR : NonHoriz P j) (hL : OpenEdgePt P i (leftEnd P q)) (hR : OpenEdgePt P j (rightEnd P q))
include hi hj nhL nhR hL hR
/-- The top height: the first obstruction of the corridor above `q`. -/
theorem exists_top_height :
    ∃ y₂, q.2 < y₂ ∧ y₂ ≤ edgeTop P i ∧ y₂ ≤ edgeTop P j ∧
      (∀ k, k < P.n → q.2 < (P.vtx k).2 → (P.vtx k).2 < y₂ →
        edgeX P i (P.vtx k).2 ≤ (P.vtx k).1 → (P.vtx k).1 ≤ edgeX P j (P.vtx k).2 → False) ∧
      (∃ k, k < P.n ∧ (P.vtx k).2 = y₂ ∧
        (edgeX P i y₂ ≤ edgeX P j y₂ → edgeX P i y₂ ≤ (P.vtx k).1 ∧ (P.vtx k).1 ≤ edgeX P j y₂)) := by
  set C : Set ℝ := {y | ∃ k, k < P.n ∧ (P.vtx k).2 = y ∧ q.2 < y ∧
    edgeX P i y ≤ (P.vtx k).1 ∧ (P.vtx k).1 ≤ edgeX P j y} ∪ {edgeTop P i, edgeTop P j} with hC
  have hfin : C.Finite := by
    refine Set.Finite.union ?_ ((finite_singleton _).insert _)
    refine ((Finset.range P.n).finite_toSet.image (fun k => (P.vtx k).2)).subset ?_
    grind
  have hne : C.Nonempty := ⟨edgeTop P i, Or.inr (Or.inl rfl)⟩
  obtain ⟨y₂, hy₂C, hmin⟩ := Set.exists_min_image C id hfin hne
  have hqi : q.2 < edgeTop P i := by
    have := ((openEdgePt_iff_edgeX nhL).1 hL).1.2
    grind [leftEnd_snd]
  have hqj : q.2 < edgeTop P j := by
    have := ((openEdgePt_iff_edgeX nhR).1 hR).1.2
    grind [rightEnd_snd]
  have hall : ∀ y ∈ C, q.2 < y := by
    grind
  refine ⟨y₂, hall _ hy₂C, hmin _ (Or.inr (Or.inl rfl)), hmin _ (Or.inr (Or.inr rfl)), ?_, ?_⟩
  · grind
  · rcases hy₂C with ⟨k, hk, hky, -, h3, h4⟩ | h
    · grind
    · simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with rfl | rfl
      · obtain ⟨k, hk, hky, hkx⟩ := exists_vtx_edgeTop hi nhL
        grind
      · obtain ⟨k, hk, hky, hkx⟩ := exists_vtx_edgeTop hj nhR
        grind

/-- The bottom height: the first obstruction of the corridor below `q`. -/
theorem exists_bot_height :
    ∃ y₁, y₁ < q.2 ∧ edgeBot P i ≤ y₁ ∧ edgeBot P j ≤ y₁ ∧
      (∀ k, k < P.n → y₁ < (P.vtx k).2 → (P.vtx k).2 < q.2 →
        edgeX P i (P.vtx k).2 ≤ (P.vtx k).1 → (P.vtx k).1 ≤ edgeX P j (P.vtx k).2 → False) ∧
      (∃ k, k < P.n ∧ (P.vtx k).2 = y₁ ∧
        (edgeX P i y₁ ≤ edgeX P j y₁ → edgeX P i y₁ ≤ (P.vtx k).1 ∧ (P.vtx k).1 ≤ edgeX P j y₁)) := by
  set C : Set ℝ := {y | ∃ k, k < P.n ∧ (P.vtx k).2 = y ∧ y < q.2 ∧
    edgeX P i y ≤ (P.vtx k).1 ∧ (P.vtx k).1 ≤ edgeX P j y} ∪ {edgeBot P i, edgeBot P j} with hC
  have hfin : C.Finite := by
    refine Set.Finite.union ?_ ((finite_singleton _).insert _)
    refine ((Finset.range P.n).finite_toSet.image (fun k => (P.vtx k).2)).subset ?_
    grind
  have hne : C.Nonempty := ⟨edgeBot P i, Or.inr (Or.inl rfl)⟩
  obtain ⟨y₁, hy₁C, hmax⟩ := Set.exists_max_image C id hfin hne
  have hqi : edgeBot P i < q.2 := by
    have := ((openEdgePt_iff_edgeX nhL).1 hL).1.1
    grind [leftEnd_snd]
  have hqj : edgeBot P j < q.2 := by
    have := ((openEdgePt_iff_edgeX nhR).1 hR).1.1
    grind [rightEnd_snd]
  have hall : ∀ y ∈ C, y < q.2 := by
    grind
  refine ⟨y₁, hall _ hy₁C, hmax _ (Or.inr (Or.inl rfl)), hmax _ (Or.inr (Or.inr rfl)), ?_, ?_⟩
  · grind
  · rcases hy₁C with ⟨k, hk, hky, -, h3, h4⟩ | h
    · grind
    · simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with rfl | rfl
      · obtain ⟨k, hk, hky, hkx⟩ := exists_vtx_edgeBot hi nhL
        grind
      · obtain ⟨k, hk, hky, hkx⟩ := exists_vtx_edgeBot hj nhR
        grind


end

/-- **Every free point has trapezoid data.** -/
theorem exists_isTrap {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ freeRegion P) :
    ∃ i j y₁ y₂, IsTrap P q i j y₁ y₂ := by
  obtain ⟨i, hi, hL, nhL⟩ := exists_leftEdge hP hq
  obtain ⟨j, hj, hR, nhR⟩ := exists_rightEdge hP hq
  obtain ⟨y₂, hq2, htopL, htopR, hnoT, htopV⟩ := exists_top_height hi hj nhL nhR hL hR
  obtain ⟨y₁, hq1, hbotL, hbotR, hnoB, hbotV⟩ := exists_bot_height hi hj nhL nhR hL hR
  refine ⟨i, j, y₁, y₂, ⟨hi, hj, nhL, nhR, hL, hR, hq1, hq2, hbotL, hbotR, htopL, htopR, ?_, htopV,
    hbotV⟩⟩
  intro k hk h1 h2 h3 h4
  rcases lt_trichotomy (P.vtx k).2 q.2 with hlt | heq | hgt
  · grind
  · rw [heq, ← leftEnd_fst_eq_edgeX nhL hL] at h3
    rw [heq, ← rightEnd_fst_eq_edgeX nhR hR] at h4
    exact not_vtx_mem_closedHSeg hP hq hk heq h3 h4
  grind

/-! ### Leaving an open convex set along a segment -/

/-- **Segment exit.**  A segment `lerp u w` through a point of an open convex set `T` meets `T`
in a parameter interval `(s₁, s₂)`; the points at `s₁`, `s₂` are in the closure of `T`, and each
is an endpoint of the segment or lies outside `T`. -/
theorem segment_exit {T : Set Point} (hT : IsOpen T) (hc : Convex ℝ T) (u w : Point) {s₀ : ℝ}
    (h0 : 0 ≤ s₀) (h1 : s₀ ≤ 1) (hs₀ : lerp u w s₀ ∈ T) :
    ∃ s₁ s₂, 0 ≤ s₁ ∧ s₁ ≤ s₀ ∧ s₀ ≤ s₂ ∧ s₂ ≤ 1 ∧
      (∀ s, s₁ < s → s < s₂ → lerp u w s ∈ T) ∧
      lerp u w s₁ ∈ closure T ∧ lerp u w s₂ ∈ closure T ∧
      (s₁ = 0 ∨ lerp u w s₁ ∉ T) ∧ (s₂ = 1 ∨ lerp u w s₂ ∉ T) := by
  set S : Set ℝ := {s | 0 ≤ s ∧ s ≤ 1 ∧ lerp u w s ∈ T} with hS
  have hs₀S : s₀ ∈ S := ⟨h0, h1, hs₀⟩
  have hSne : S.Nonempty := ⟨s₀, hs₀S⟩
  have hbb : BddBelow S := ⟨0, fun s hs => hs.1⟩
  have hba : BddAbove S := ⟨1, fun s hs => hs.2.1⟩
  have hSconv : Convex ℝ S := by
    intro s hs s' hs' a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    refine ⟨?_, ?_, ?_⟩
    · show 0 ≤ a * s + (1 - a) * s'
      nlinarith [mul_nonneg ha hs.1, mul_nonneg hb hs'.1]
    · show a * s + (1 - a) * s' ≤ 1
      nlinarith [mul_le_mul_of_nonneg_left hs.2.1 ha, mul_le_mul_of_nonneg_left hs'.2.1 hb]
    · show lerp u w (a • s + (1 - a) • s') ∈ T
      have e : lerp u w (a • s + (1 - a) • s') = a • lerp u w s + (1 - a) • lerp u w s' := by
        rw [point_ext_iff]
        simp only [smul_eq_mul, lerp_fst, lerp_snd, Geometry.add_fst, Geometry.add_snd,
          Geometry.smul_fst, Geometry.smul_snd]
        grind
      rw [e]
      exact hc hs.2.2 hs'.2.2 ha hb hab
  have hord := hSconv.ordConnected
  have hcont : Continuous (lerp u w) := continuous_lerp u w
  refine ⟨sInf S, sSup S, le_csInf hSne (fun s hs => hs.1), csInf_le hbb hs₀S, le_csSup hba hs₀S,
    csSup_le hSne (fun s hs => hs.2.1), ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs1 hs2
    obtain ⟨a, haS, has⟩ := exists_lt_of_csInf_lt hSne hs1
    obtain ⟨b, hbS, hsb⟩ := exists_lt_of_lt_csSup hSne hs2
    exact (hord.out haS hbS ⟨has.le, hsb.le⟩).2.2
  · rcases (csInf_le hbb hs₀S).lt_or_eq with hlt | heq
    · refine mem_closure_of_tendsto (b := 𝓝[>] (sInf S))
        ((hcont.tendsto _).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [Ioo_mem_nhdsGT hlt] with s hs
      obtain ⟨a, haS, has⟩ := exists_lt_of_csInf_lt hSne hs.1
      exact (hord.out haS hs₀S ⟨has.le, hs.2.le⟩).2.2
    · rw [heq]; exact subset_closure hs₀
  · rcases (le_csSup hba hs₀S).lt_or_eq with hlt | heq
    · refine mem_closure_of_tendsto (b := 𝓝[<] (sSup S))
        ((hcont.tendsto _).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [Ioo_mem_nhdsLT hlt] with s hs
      obtain ⟨b, hbS, hsb⟩ := exists_lt_of_lt_csSup hSne hs.2
      exact (hord.out hs₀S hbS ⟨hs.1.le, hsb.le⟩).2.2
    · rw [← heq]; exact subset_closure hs₀
  · by_contra hcon
    rw [not_or, not_not] at hcon
    obtain ⟨hne0, hmem⟩ := hcon
    have hpos : 0 < sInf S := lt_of_le_of_ne (le_csInf hSne (fun s hs => hs.1)) (Ne.symm hne0)
    have hev : ∀ᶠ s in 𝓝 (sInf S), lerp u w s ∈ T :=
      hcont.continuousAt.preimage_mem_nhds (hT.mem_nhds hmem)
    obtain ⟨s, hsT, hs⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT hpos)).exists
    have hsS : s ∈ S := ⟨hs.1.le, (hs.2.le.trans (csInf_le hbb hs₀S)).trans h1, hsT⟩
    exact absurd (csInf_le hbb hsS) (not_le.2 hs.2)
  · by_contra hcon
    rw [not_or, not_not] at hcon
    obtain ⟨hne1, hmem⟩ := hcon
    have hlt1 : sSup S < 1 := lt_of_le_of_ne (csSup_le hSne (fun s hs => hs.2.1)) hne1
    have hev : ∀ᶠ s in 𝓝 (sSup S), lerp u w s ∈ T :=
      hcont.continuousAt.preimage_mem_nhds (hT.mem_nhds hmem)
    obtain ⟨s, hsT, hs⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hlt1)).exists
    have hsS : s ∈ S := ⟨h0.trans ((le_csSup hba hs₀S).trans hs.1.le), hs.2.le, hsT⟩
    exact absurd (le_csSup hba hsS) (not_le.2 hs.1)

/-! ### The trapezoid is free -/

namespace IsTrap

variable {P : Polygon} {q : Point} {i j : ℕ} {y₁ y₂ : ℝ}

/-- No point of an edge other than `i`, `j` lies in the closed trapezoid at the height of `q`. -/
theorem no_edge_at_base (hP : P.Simple) (hq : q ∈ freeRegion P) (h : IsTrap P q i j y₁ y₂)
    {k : ℕ} (hk : k < P.n) (hki : k ≠ i) (hkj : k ≠ j) {z : Point} (hz : z ∈ P.edge k)
    (hzc : z ∈ closedTrap P i j y₁ y₂) (hzy : z.2 = q.2) : False := by
  obtain ⟨-, -, h3, h4⟩ := hzc
  rw [hzy, ← h.leftEnd_eq] at h3
  rw [hzy, ← h.rightEnd_eq] at h4
  rcases closedHSeg_inter_boundary hP hq.1 hzy h3 h4 ⟨k, hk, hz⟩ with e | e
  · rw [e] at hz
    exact h.left_mem.not_mem_other hP h.hi hk hki hz
  · rw [e] at hz
    exact h.right_mem.not_mem_other hP h.hj hk hkj hz

/-- No point of an edge other than `i`, `j` lies in the closed trapezoid strictly between the
two heights if it is a vertex or outside the open trapezoid. -/
theorem no_band_point (hP : P.Simple) (h : IsTrap P q i j y₁ y₂) {k : ℕ} (hk : k < P.n)
    (hki : k ≠ i) (hkj : k ≠ j) {x : Point} (hx : x ∈ P.edge k)
    (hxc : x ∈ closedTrap P i j y₁ y₂) (h1 : y₁ < x.2) (h2 : x.2 < y₂)
    (hv : x = P.vtx k ∨ x = P.vtx ((k + 1) % P.n) ∨ x ∉ trapSet P i j y₁ y₂) : False := by
  obtain ⟨-, -, h3, h4⟩ := hxc
  have hvert : ∃ m, m < P.n ∧ x = P.vtx m := by
    rcases hv with hv | hv | hv
    · grind
    · exact ⟨(k + 1) % P.n, succIdx_lt P hk, hv⟩
    · have hor : x.1 = edgeX P i x.2 ∨ x.1 = edgeX P j x.2 := by
        by_contra hne
        rw [not_or] at hne
        exact hv ⟨h1, h2, lt_of_le_of_ne h3 (Ne.symm hne.1), lt_of_le_of_ne h4 hne.2⟩
      rcases hor with hor | hor
      · rcases simple_endpoint_of_mem_two hP hk h.hi hki hx (h.mem_edgeL h1.le h2.le hor) with e | e
        · grind
        · exact ⟨_, succIdx_lt P hk, e⟩
      · rcases simple_endpoint_of_mem_two hP hk h.hj hkj hx (h.mem_edgeR h1.le h2.le hor) with e | e
        · grind
        · exact ⟨_, succIdx_lt P hk, e⟩
  obtain ⟨m, hm, rfl⟩ := hvert
  exact h.no_vertex m hm h1 h2 h3 h4

section
variable (hP : P.Simple) (hq : q ∈ freeRegion P) (h : IsTrap P q i j y₁ y₂)
include hP hq h
/-- **The trapezoid contains no boundary point.** -/
theorem not_mem_boundary
    {p : Point} (hp : p ∈ trapSet P i j y₁ y₂) : p ∉ P.boundary := by
  rintro ⟨k, hk, hpk⟩
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  have hki : k ≠ i := by
    rintro rfl
    have := ((mem_edge_iff_edgeX h.nhL).1 hpk).2
    linarith
  have hkj : k ≠ j := by
    rintro rfl
    have := ((mem_edge_iff_edgeX h.nhR).1 hpk).2
    linarith
  obtain ⟨s₀, hs0, hs1, hps⟩ := hpk
  have hps' : p = lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₀ := hps
  have hpT : lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₀ ∈ trapSet P i j y₁ y₂ := by
    rw [← hps']; exact ⟨hp1, hp2, hp3, hp4⟩
  obtain ⟨s₁, s₂, hs₁0, hs₁, hs₂, hs₂1, hT, hc₁, hc₂, hv₁, hv₂⟩ :=
    segment_exit (isOpen_trapSet P i j y₁ y₂) (convex_trapSet P i j y₁ y₂) (P.vtx k)
      (P.vtx ((k + 1) % P.n)) hs0 hs1 hpT
  have hsub := closure_trapSet_subset P i j y₁ y₂
  have hx₁e : lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₁ ∈ P.edge k :=
    lerp_mem_segment _ _ hs₁0 (hs₁.trans (hs₂.trans hs₂1))
  have hx₂e : lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₂ ∈ P.edge k :=
    lerp_mem_segment _ _ (hs₁0.trans (hs₁.trans hs₂)) hs₂1
  have hx₁c := hsub hc₁
  have hx₂c := hsub hc₂
  have hv₁' : lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₁ = P.vtx k ∨
      lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₁ = P.vtx ((k + 1) % P.n) ∨
      lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₁ ∉ trapSet P i j y₁ y₂ := by
    rcases hv₁ with e | hv
    · left; rw [e, lerp_zero]
    grind
  have hv₂' : lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₂ = P.vtx k ∨
      lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₂ = P.vtx ((k + 1) % P.n) ∨
      lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₂ ∉ trapSet P i j y₁ y₂ := by
    rcases hv₂ with e | hv
    · right; left; rw [e, lerp_one]
    grind
  have hcont : ContinuousOn (fun s => (lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s).2) (Icc s₁ s₂) :=
    (continuous_lerp _ _).snd.continuousOn
  -- the height of `p` lies between the heights of the two exit points
  have hbetween : ((lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₁).2 ≤ p.2 ∧
      p.2 ≤ (lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₂).2) ∨
      ((lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₂).2 ≤ p.2 ∧
      p.2 ≤ (lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₁).2) := by
    rw [hps']
    simp only [lerp_snd]
    rcases le_total (P.vtx k).2 (P.vtx ((k + 1) % P.n)).2 with hd | hd
    · left
      constructor <;> nlinarith [mul_le_mul_of_nonneg_right hs₁ (sub_nonneg.2 hd),
        mul_le_mul_of_nonneg_right hs₂ (sub_nonneg.2 hd)]
    · right
      constructor <;> nlinarith [mul_le_mul_of_nonpos_right hs₁ (sub_nonpos.2 hd),
        mul_le_mul_of_nonpos_right hs₂ (sub_nonpos.2 hd)]
  -- if the height of `q` is reached, the edge meets the closed trapezoid at that height
  have hIVT : ((lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₁).2 ≤ q.2 ∧
      q.2 ≤ (lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₂).2) ∨
      ((lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₂).2 ≤ q.2 ∧
      q.2 ≤ (lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₁).2) → False := by
    intro hA
    have hex : ∃ s ∈ Icc s₁ s₂, (lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s).2 = q.2 := by
      rcases hA with hA | hA
      · exact intermediate_value_Icc (hs₁.trans hs₂) hcont hA
      · exact intermediate_value_Icc' (hs₁.trans hs₂) hcont hA
    obtain ⟨s, ⟨hsa, hsb⟩, hsy⟩ := hex
    have hze : lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s ∈ P.edge k :=
      lerp_mem_segment _ _ (hs₁0.trans hsa) (hsb.trans hs₂1)
    have hzc : lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s ∈ closedTrap P i j y₁ y₂ := by
      rcases hsa.lt_or_eq with hlt | heq
      · rcases hsb.lt_or_eq with hlt2 | heq2
        · exact trapSet_subset_closedTrap _ _ _ _ _ (hT s hlt hlt2)
        grind
      grind
    exact h.no_edge_at_base hP hq hk hki hkj hze hzc hsy
  by_cases hA : ((lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₁).2 ≤ q.2 ∧
      q.2 ≤ (lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₂).2) ∨
      ((lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₂).2 ≤ q.2 ∧
      q.2 ≤ (lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₁).2)
  · exact hIVT hA
  · rw [not_or] at hA
    obtain ⟨hA1, hA2⟩ := hA
    have key : ∀ x, x ∈ P.edge k → x ∈ closedTrap P i j y₁ y₂ →
        (x = P.vtx k ∨ x = P.vtx ((k + 1) % P.n) ∨ x ∉ trapSet P i j y₁ y₂) →
        y₁ < x.2 → x.2 < y₂ → False :=
      fun x hx hxc hv h1 h2 => h.no_band_point hP hk hki hkj hx hxc h1 h2 hv
    have hb := h.bot_lt
    have ht := h.lt_top
    rcases hbetween with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
    · rcases le_or_gt (lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₁).2 q.2 with hx | hx
      · have : (lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₂).2 < q.2 := by
          grind
        exact key _ hx₂e hx₂c hv₂' (by linarith) (by linarith)
      · exact key _ hx₁e hx₁c hv₁' (by linarith) (by linarith)
    · rcases le_or_gt (lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₂).2 q.2 with hx | hx
      · have : (lerp (P.vtx k) (P.vtx ((k + 1) % P.n)) s₁).2 < q.2 := by
          grind
        exact key _ hx₁e hx₁c hv₁' (by linarith) (by linarith)
      · exact key _ hx₂e hx₂c hv₂' (by linarith) (by linarith)

/-- **The trapezoid is interior.** -/
theorem trapSet_subset_interior : trapSet P i j y₁ y₂ ⊆ P.filled \ P.boundary :=
  subset_interior_of_isPreconnected hP (convex_trapSet P i j y₁ y₂).isPreconnected
    (fun _ hp => h.not_mem_boundary hP hq hp) (h.q_mem hP hq.1) hq.1

/-- **The trapezoid is free**: it contains no chord point either. -/
theorem trapSet_subset_freeRegion : trapSet P i j y₁ y₂ ⊆ freeRegion P := by
  intro p hp
  refine ⟨h.trapSet_subset_interior hP hq hp, ?_⟩
  rintro ⟨S, hS, hpS⟩
  obtain ⟨m, σ, hm, hσ, hdir, rfl, hch⟩ := chords_spec hP hS
  rw [chordSet_eq_hseg] at hpS
  obtain ⟨hy, ha, hb⟩ := hpS
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  -- the emitting vertex is at the height of `p`, outside the closed corridor
  have hnot : ¬ (edgeX P i (P.vtx m).2 ≤ (P.vtx m).1 ∧ (P.vtx m).1 ≤ edgeX P j (P.vtx m).2) :=
    fun hh => h.no_vertex m hm (hy ▸ hp1) (hy ▸ hp2) hh.1 hh.2
  rw [← hy, not_and_or, not_le, not_le] at hnot
  have hbL : ((edgeX P i p.2, p.2) : Point) ∈ P.boundary :=
    ⟨i, h.hi, h.mem_edgeL hp1.le hp2.le rfl⟩
  have hbR : ((edgeX P j p.2, p.2) : Point) ∈ P.boundary :=
    ⟨j, h.hj, h.mem_edgeR hp1.le hp2.le rfl⟩
  have hminle := min_le_left (P.vtx m).1 (chordEnd P m σ).1
  have hlemax := le_max_left (P.vtx m).1 (chordEnd P m σ).1
  rcases hnot with hlt | hlt
  · -- the vertex is the left endpoint of the chord, and the left side of the corridor is inside
    
    have hint := hch.open_int (edgeX P i p.2) (by grind) (by linarith)
    grind
  · 
    have hint := hch.open_int (edgeX P j p.2) (by linarith) (by grind)
    grind


end

end IsTrap

/-! ### The open top and bottom sides contain no free point -/

/-- A point `e` of an open non-horizontal edge such that all nearby points on one side (`ε`) of
the horizontal line through `e` lie in an interior set `U`: impossible, since the edge itself
has points on that side near `e`. -/
theorem side_edge_false {P : Polygon} {y₀ ε : ℝ} (hε : ε = 1 ∨ ε = -1) {U : Set Point}
    (hU : U ⊆ P.filled \ P.boundary) {e : Point} (hey : e.2 = y₀)
    (hnear : ∀ᶠ p' in 𝓝 e, 0 < ε * (p'.2 - y₀) → p' ∈ U) {j : ℕ} (hj : j < P.n)
    (hnh : NonHoriz P j) (he : OpenEdgePt P j e) : False := by
  obtain ⟨t, ht, rfl⟩ := he
  set u := P.vtx j with hu
  set w := P.vtx ((j + 1) % P.n) with hw
  have hd0 : w.2 - u.2 ≠ 0 := sub_ne_zero.2 (Ne.symm hnh)
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hcont : Continuous fun η : ℝ => lerp u w (t + ε * (w.2 - u.2) * η) :=
    (continuous_lerp u w).comp (by fun_prop)
  have htend : Tendsto (fun η : ℝ => lerp u w (t + ε * (w.2 - u.2) * η)) (𝓝[>] 0)
      (𝓝 (lerp u w t)) := by
    have := hcont.tendsto 0
    simp only [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev1 := htend.eventually hnear
  have hev2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), t + ε * (w.2 - u.2) * η ∈ Ioo (0 : ℝ) 1 := by
    have hc : Continuous fun η : ℝ => t + ε * (w.2 - u.2) * η := by fun_prop
    have : Tendsto (fun η : ℝ => t + ε * (w.2 - u.2) * η) (𝓝[>] 0) (𝓝 t) := by
      have := hc.tendsto 0
      simp only [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact this.eventually (isOpen_Ioo.mem_nhds ht)
  obtain ⟨η, hη1, hη2, hη0⟩ := (hev1.and (hev2.and self_mem_nhdsWithin)).exists
  have hη0' : (0 : ℝ) < η := hη0
  have hpos : 0 < ε * ((lerp u w (t + ε * (w.2 - u.2) * η)).2 - y₀) := by
    rw [← hey]
    simp only [lerp_snd]
    have : ε * ((u.2 + (t + ε * (w.2 - u.2) * η) * (w.2 - u.2)) - (u.2 + t * (w.2 - u.2))) =
        (ε * ε) * ((w.2 - u.2) * (w.2 - u.2)) * η := by ring
    rw [this, hε2, one_mul]
    exact mul_pos (mul_self_pos.2 hd0) hη0'
  have hmem := hU (hη1 hpos)
  exact hmem.2 ⟨j, hj, lerp_mem_segment _ _ hη2.1.le hη2.2.le⟩

/-- **Side lemma.**  Let `(a, b) × {y₀}` be an open horizontal side of an interior set `U`, in
the sense that near every point of the side, all points on the side `ε` of the line are in `U`,
and let some vertex lie on the closed side.  Then no point of the open side is free. -/
theorem not_free_of_side {P : Polygon} (hP : P.Simple) {y₀ a b ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {U : Set Point} (hU : U ⊆ P.filled \ P.boundary)
    (hnear : ∀ x, a < x → x < b →
      ∀ᶠ p' in 𝓝 ((x, y₀) : Point), 0 < ε * (p'.2 - y₀) → p' ∈ U)
    {m : ℕ} (hm : m < P.n) (hmy : (P.vtx m).2 = y₀) (hma : a ≤ (P.vtx m).1)
    (hmb : (P.vtx m).1 ≤ b) {p : Point} (hp : p ∈ freeRegion P) (hpy : p.2 = y₀) (hpa : a < p.1)
    (hpb : p.1 < b) : False := by
  have hnot : ¬ ((leftEnd P p).1 ≤ (P.vtx m).1 ∧ (P.vtx m).1 ≤ (rightEnd P p).1) :=
    fun hh => not_vtx_mem_closedHSeg hP hp hm (hmy.trans hpy.symm) hh.1 hh.2
  rw [not_and_or, not_le, not_le] at hnot
  rcases hnot with hlt | hlt
  · obtain ⟨i, hi, hL, hnh⟩ := exists_leftEdge hP hp
    have hle : (leftEnd P p).1 < p.1 := leftEnd_fst_lt hP hp.1
    have he : (((leftEnd P p).1, y₀) : Point) = leftEnd P p := point_ext rfl hpy.symm
    have := hnear (leftEnd P p).1 (by linarith) (by linarith)
    rw [he] at this
    exact side_edge_false hε hU (by grind) this hi hnh hL
  · obtain ⟨j, hj, hR, hnh⟩ := exists_rightEdge hP hp
    have hle : p.1 < (rightEnd P p).1 := lt_rightEnd_fst hP hp.1
    have he : (((rightEnd P p).1, y₀) : Point) = rightEnd P p := point_ext rfl hpy.symm
    have := hnear (rightEnd P p).1 (by linarith) (by linarith)
    rw [he] at this
    exact side_edge_false hε hU (by grind) this hj hnh hR

namespace IsTrap

variable {P : Polygon} {q : Point} {i j : ℕ} {y₁ y₂ : ℝ}

section
variable (h : IsTrap P q i j y₁ y₂) {x : ℝ}
include h
/-- Near a point of the open top side, the points below the top height are in the trapezoid. -/
theorem near_top (hx1 : edgeX P i y₂ < x)
    (hx2 : x < edgeX P j y₂) :
    ∀ᶠ p' in 𝓝 ((x, y₂) : Point), 0 < (-1) * (p'.2 - y₂) → p' ∈ trapSet P i j y₁ y₂ := by
  have hopen : IsOpen {p' : Point | y₁ < p'.2 ∧ edgeX P i p'.2 < p'.1 ∧ p'.1 < edgeX P j p'.2} := by
    have h1 : IsOpen {p : Point | y₁ < p.2} := isOpen_lt continuous_const continuous_snd
    have h3 : IsOpen {p : Point | edgeX P i p.2 < p.1} :=
      isOpen_lt ((continuous_edgeX P i).comp continuous_snd) continuous_fst
    have h4 : IsOpen {p : Point | p.1 < edgeX P j p.2} :=
      isOpen_lt continuous_fst ((continuous_edgeX P j).comp continuous_snd)
    exact h1.inter (h3.inter h4)
  have hmem : ((x, y₂) : Point) ∈
      {p' : Point | y₁ < p'.2 ∧ edgeX P i p'.2 < p'.1 ∧ p'.1 < edgeX P j p'.2} :=
    ⟨h.bot_lt.trans h.lt_top, hx1, hx2⟩
  filter_upwards [hopen.mem_nhds hmem] with p' hp' hpos
  exact ⟨hp'.1, by linarith, hp'.2.1, hp'.2.2⟩

/-- Near a point of the open bottom side, the points above the bottom height are in the
trapezoid. -/
theorem near_bot (hx1 : edgeX P i y₁ < x)
    (hx2 : x < edgeX P j y₁) :
    ∀ᶠ p' in 𝓝 ((x, y₁) : Point), 0 < 1 * (p'.2 - y₁) → p' ∈ trapSet P i j y₁ y₂ := by
  have hopen : IsOpen {p' : Point | p'.2 < y₂ ∧ edgeX P i p'.2 < p'.1 ∧ p'.1 < edgeX P j p'.2} := by
    have h2 : IsOpen {p : Point | p.2 < y₂} := isOpen_lt continuous_snd continuous_const
    have h3 : IsOpen {p : Point | edgeX P i p.2 < p.1} :=
      isOpen_lt ((continuous_edgeX P i).comp continuous_snd) continuous_fst
    have h4 : IsOpen {p : Point | p.1 < edgeX P j p.2} :=
      isOpen_lt continuous_fst ((continuous_edgeX P j).comp continuous_snd)
    exact h2.inter (h3.inter h4)
  have hmem : ((x, y₁) : Point) ∈
      {p' : Point | p'.2 < y₂ ∧ edgeX P i p'.2 < p'.1 ∧ p'.1 < edgeX P j p'.2} :=
    ⟨h.bot_lt.trans h.lt_top, hx1, hx2⟩
  filter_upwards [hopen.mem_nhds hmem] with p' hp' hpos
  exact ⟨by linarith, hp'.1, hp'.2.1, hp'.2.2⟩


end

section
variable (hP : P.Simple) (hq : q ∈ freeRegion P) (h : IsTrap P q i j y₁ y₂)
include hP hq h
/-- **A free point of the closure of the trapezoid lies in the trapezoid.** -/
theorem closure_inter_free :
    closure (trapSet P i j y₁ y₂) ∩ freeRegion P ⊆ trapSet P i j y₁ y₂ := by
  rintro p ⟨hpc, hpf⟩
  obtain ⟨h1, h2, h3, h4⟩ := closure_trapSet_subset P i j y₁ y₂ hpc
  have hnotL : p.1 ≠ edgeX P i p.2 := fun e => hpf.1.2 ⟨i, h.hi, h.mem_edgeL h1 h2 e⟩
  have hnotR : p.1 ≠ edgeX P j p.2 := fun e => hpf.1.2 ⟨j, h.hj, h.mem_edgeR h1 h2 e⟩
  have h3' : edgeX P i p.2 < p.1 := lt_of_le_of_ne h3 (Ne.symm hnotL)
  have h4' : p.1 < edgeX P j p.2 := lt_of_le_of_ne h4 hnotR
  refine ⟨?_, ?_, h3', h4'⟩
  · rcases h1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [← heq] at h3' h4'
      obtain ⟨m, hm, hmy, hmx⟩ := h.bot_vertex
      obtain ⟨hma, hmb⟩ := hmx (h3'.trans h4').le
      exact not_free_of_side hP (Or.inl rfl) (h.trapSet_subset_interior hP hq)
        (fun x hx1 hx2 => h.near_bot hx1 hx2) hm hmy hma hmb hpf heq.symm h3' h4'
  · rcases h2.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [heq] at h3' h4'
      obtain ⟨m, hm, hmy, hmx⟩ := h.top_vertex
      obtain ⟨hma, hmb⟩ := hmx (h3'.trans h4').le
      exact not_free_of_side hP (Or.inr rfl) (h.trapSet_subset_interior hP hq)
        (fun x hx1 hx2 => h.near_top hx1 hx2) hm hmy hma hmb hpf heq h3' h4'

/-- **The region of `q` is exactly the trapezoid.** -/
theorem region_eq :
    connectedComponentIn (freeRegion P) q = trapSet P i j y₁ y₂ := by
  apply Subset.antisymm
  · refine IsPreconnected.subset_left_of_subset_union (isOpen_trapSet P i j y₁ y₂)
      isClosed_closure.isOpen_compl (disjoint_compl_right.mono_left subset_closure) ?_
      ⟨q, mem_connectedComponentIn hq, h.q_mem hP hq.1⟩ isPreconnected_connectedComponentIn
    intro p hp
    by_cases hpc : p ∈ closure (trapSet P i j y₁ y₂)
    · exact Or.inl (h.closure_inter_free hP hq ⟨hpc, connectedComponentIn_subset _ _ hp⟩)
    simp_all
  · exact (convex_trapSet P i j y₁ y₂).isPreconnected.subset_connectedComponentIn
      (h.q_mem hP hq.1) (h.trapSet_subset_freeRegion hP hq)

/-- The closure of the trapezoid lies in the filled region. -/
theorem closure_subset_filled :
    closure (trapSet P i j y₁ y₂) ⊆ P.filled :=
  closure_minimal (fun _ hp => (h.trapSet_subset_interior hP hq hp).1) (isClosed_filled P)


end

section
variable (h : IsTrap P q i j y₁ y₂) {x : ℝ}
include h
/-- A point of the open top side is in the closure of the trapezoid. -/
theorem top_mem_closure (hx1 : edgeX P i y₂ < x)
    (hx2 : x < edgeX P j y₂) : ((x, y₂) : Point) ∈ closure (trapSet P i j y₁ y₂) := by
  have hcont : Continuous fun η : ℝ => ((x, y₂ - η) : Point) := by fun_prop
  have htend : Tendsto (fun η : ℝ => ((x, y₂ - η) : Point)) (𝓝[>] 0) (𝓝 (x, y₂)) := by
    have := hcont.tendsto 0
    simp only [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto htend ?_
  have hev := htend.eventually (h.near_top hx1 hx2)
  filter_upwards [hev, self_mem_nhdsWithin] with η hη hη0
  simp_all

/-- A point of the open bottom side is in the closure of the trapezoid. -/
theorem bot_mem_closure (hx1 : edgeX P i y₁ < x)
    (hx2 : x < edgeX P j y₁) : ((x, y₁) : Point) ∈ closure (trapSet P i j y₁ y₂) := by
  have hcont : Continuous fun η : ℝ => ((x, y₁ + η) : Point) := by fun_prop
  have htend : Tendsto (fun η : ℝ => ((x, y₁ + η) : Point)) (𝓝[>] 0) (𝓝 (x, y₁)) := by
    have := hcont.tendsto 0
    simp only [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto htend ?_
  have hev := htend.eventually (h.near_bot hx1 hx2)
  filter_upwards [hev, self_mem_nhdsWithin] with η hη hη0
  simp_all


end

section
variable (hP : P.Simple) (hq : q ∈ freeRegion P) (h : IsTrap P q i j y₁ y₂) {x : ℝ}
include hP hq h
/-- **The open top side consists of boundary points and chord points.** -/
theorem top_side
    (hx1 : edgeX P i y₂ < x) (hx2 : x < edgeX P j y₂) :
    ((x, y₂) : Point) ∈ P.boundary ∪ chordUnion P := by
  by_contra hcon
  rw [mem_union, not_or] at hcon
  have hc := h.top_mem_closure hx1 hx2
  have hfree : ((x, y₂) : Point) ∈ freeRegion P :=
    ⟨⟨h.closure_subset_filled hP hq hc, hcon.1⟩, hcon.2⟩
  have := h.closure_inter_free hP hq ⟨hc, hfree⟩
  exact lt_irrefl _ this.2.1

/-- **The open bottom side consists of boundary points and chord points.** -/
theorem bot_side
    (hx1 : edgeX P i y₁ < x) (hx2 : x < edgeX P j y₁) :
    ((x, y₁) : Point) ∈ P.boundary ∪ chordUnion P := by
  by_contra hcon
  rw [mem_union, not_or] at hcon
  have hc := h.bot_mem_closure hx1 hx2
  have hfree : ((x, y₁) : Point) ∈ freeRegion P :=
    ⟨⟨h.closure_subset_filled hP hq hc, hcon.1⟩, hcon.2⟩
  have := h.closure_inter_free hP hq ⟨hc, hfree⟩
  exact lt_irrefl _ this.1


end

end IsTrap

/-! ### The main theorems -/

section
variable {P : Polygon} (hP : P.Simple)
include hP
/-- **The region of a free point is an open trapezoid.** -/
theorem exists_isTrap_region_eq {q : Point}
    (hq : q ∈ freeRegion P) :
    ∃ i j y₁ y₂, IsTrap P q i j y₁ y₂ ∧
      connectedComponentIn (freeRegion P) q = trapSet P i j y₁ y₂ := by
  grind [Chazelle.Visibility.exists_isTrap, Chazelle.Visibility.IsTrap.region_eq]

/-- **Every region of the horizontal visibility map is an open trapezoid**: for some free point
`q` with trapezoid data `i, j, y₁, y₂`, the region is
`{p | y₁ < p.2 < y₂ ∧ edgeX P i p.2 < p.1 < edgeX P j p.2}`. -/
theorem regions_eq_trapSet {C : Set Point} (hC : C ∈ regions P) :
    ∃ q i j y₁ y₂, q ∈ freeRegion P ∧ IsTrap P q i j y₁ y₂ ∧ C = trapSet P i j y₁ y₂ := by
  obtain ⟨q, hq, rfl⟩ := hC
  grind [Chazelle.Visibility.exists_isTrap_region_eq]


end

end

end Chazelle.Visibility
