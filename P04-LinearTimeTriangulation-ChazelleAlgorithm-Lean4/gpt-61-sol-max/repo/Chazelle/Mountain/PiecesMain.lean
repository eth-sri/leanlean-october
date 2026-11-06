module

public meta import Chazelle.Arithmetic

public import Chazelle.Mountain.PieceSteps

/-!
# The mountain decomposition theorem

Let `P` be a simple polygon and `l` a piece of the subdivision of `P` by the inserted diagonals
`allDiagonals P` (`IsPiece P l`, `Chazelle.Mountain.Pieces`).  We prove that the piece
`Q = subPoly P l` is a **monotone mountain** (`piece_isMonoAt`): for some position `a`, the
vertices of `Q` read cyclically from position `a + 1` to position `a` are strictly
`ylexLT`-monotone, so the edge `a` of `Q` joins the maximum to the minimum and the other chain is
monotone.

## Proof

Let `m` be the position of the `ylexLT`-lowest vertex `v` of `Q`.

1. **Initial analysis** (`piece_initial`).  Near `v` the interior of `Q` lies above `v`
   (`IsPiece.locMin_lower_exterior`); pick a free point `p` of `P` in the interior of `Q` just
   above `v`, with trapezoid `D`, so that `v` is on the closed bottom side of `D` and the segment
   from `p` to `v` stays in the interior of `Q`.  A case analysis (the cell of `D` containing `p`,
   the position of `v` on the bottom side, the diagonal of `D`) shows that `v` is the lower
   endpoint of a side edge `e` of `D` whose upper endpoint `u` is a neighbour of `v` in `Q` — the
   future **base** — and that the other neighbour `w` of `v` in `Q` is in the left or right walk
   state of `Chazelle.Mountain.PieceSteps` with respect to `e`.  (Points of the bottom side just
   to the left of `v` are `ylexLT`-below `v`; if they were in the piece, an edge of `Q` would leave
   `v` to the left, below `v`.  Points of the bottom side just to the right of `v`, when `v` is the
   bottom vertex, would force an edge of `Q` along the bottom side to a vertex to the right of the
   rightmost bottom vertex.)
2. **The walk** (`walk_chain`, `mono_of_walk`).  Walking along `Q` from `v` away from `u`, each
   vertex other than `u` is in the walk state and not on `e` (the only vertices on `e` are `v` and
   `u`), so its next neighbour is strictly `ylexLT`-higher (`StateL.step`, `StateR.step`).  Hence
   the chain from `v` around to `u` is strictly increasing: `Q` is a monotone mountain with base
   `u v`.

## Main results

* `piece_isMonoAt`: `IsPiece P l → ∃ a < l.length, IsMonoAt (subPoly P l) a`.
* `piece_isMountainAt`: `IsPiece P l → ∃ a < l.length,
    IsMountainAt (subPoly P l) a ∨ IsMountainAt (subPoly P l.reverse) a`.
* `piece_isMountain` (the form used by the stack algorithm of `Chazelle.Mountain.Stack`):
  `IsPiece P l → ∃ s, IsMountain ((subPoly P l).rotate s) ∨
    IsMountain ((subPoly P l.reverse).rotate s)`.
* Reversal: `simple_subPoly_reverse`, `boundary_subPoly_reverse`, `filled_subPoly_reverse`,
  `vtx_subPoly_reverse` (the reversed piece is simple, with the same boundary and filled region;
  generic versions `rev_simple`, `rev_boundary`, `rev_filled`, `rev_chainInc`).
-/

namespace Chazelle.Mountain

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Visibility
open Chazelle.EarClip (subPoly n_subPoly vtx_subPoly_getD)
open Chazelle.Existence (vtx_mem_boundary)
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one point_ext lerp_mem_segment
  continuous_lerp)

variable {P : Polygon}

/-! ### Geometric helpers -/

/-- If a point `z` at the height of `v` but different from `v` lies on the segment from `v` to
`a`, then `a` is at the height of `v`, on the same side of `v` as `z`. -/
theorem ray_nbr {v a z : Point} (hz2 : z.2 = v.2) (hz1 : z.1 ≠ v.1)
    (h : z ∈ Chazelle.segment v a) : a.2 = v.2 ∧ 0 < (z.1 - v.1) * (a.1 - v.1) := by
  obtain ⟨t, ht0, ht1, he⟩ := h
  
  have e2 : t * (a.2 - v.2) = 0 := by
    simp_all
  have ht : t ≠ 0 := by
    simp_all
  have ha : a.1 - v.1 ≠ 0 := by
    simp_all
  refine ⟨?_, ?_⟩
  · grind
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    simp_all [mul_assoc]

/-- **Segments to a vertex.**  Around a vertex `v` of a simple polygon there is a ball such that
for every interior point `p` in it, the half-open segment from `p` to `v` is interior. -/
theorem exists_ball_lerp_interior {Q : Polygon} (hQ : Q.Simple) {k : ℕ} (hk : k < Q.n) :
    ∃ r > 0, ∀ p ∈ ball (Q.vtx k) r, p ∈ Q.filled \ Q.boundary →
      ∀ s ∈ Ico (0 : ℝ) 1, lerp p (Q.vtx k) s ∈ Q.filled \ Q.boundary := by
  have hn := simple_three_le hQ
  set v := Q.vtx k with hv
  set a := Q.vtx (prevIdx Q k) with ha
  set b := Q.vtx ((k + 1) % Q.n) with hb
  obtain ⟨r₁, hr₁, hball⟩ := Chazelle.Existence.boundary_near_vtx hQ hk
  have hav : 0 < dist a v :=
    dist_pos.2 (simple_vtx_ne hQ (prevIdx_lt Q hk) hk (prevIdx_ne Q hn hk))
  have hbv : 0 < dist b v := dist_pos.2 (simple_vtx_succ_ne hQ hk).symm
  set r := min r₁ (min (dist a v) (dist b v)) with hr
  have hr0 : 0 < r := lt_min hr₁ (lt_min hav hbv)
  refine ⟨r, hr0, fun p hp hpi => ?_⟩
  have hpv : dist p v < r := hp
  set S := lerp p v '' Ico (0 : ℝ) 1 with hS
  have hSball : S ⊆ ball v r := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Geometry.lerp_eq_smul_add_smul]
    exact (convex_ball v r) hp (mem_ball_self hr0) (by grind) ht.1 (by ring)
  have hSb : ∀ x ∈ S, x ∉ Q.boundary := by
    rintro _ ⟨t, ht, rfl⟩ hxb
    have hx := hSball ⟨t, ht, rfl⟩
    rcases hball _ (ball_subset_ball (min_le_left _ _) hx) hxb with h | h
    · rw [Geometry.segment_comm] at h
      rcases mem_segment_or_far ht.2 h with h' | h'
      · apply hpi.2
        refine ⟨prevIdx Q k, prevIdx_lt Q hk, ?_⟩
        rw [edge_prevIdx Q hk, Geometry.segment_comm]
        exact h'
      · have : r ≤ dist a v := (min_le_right _ _).trans (min_le_left _ _)
        linarith
    · rcases mem_segment_or_far ht.2 h with h' | h'
      · exact hpi.2 ⟨k, hk, h'⟩
      · have : r ≤ dist b v := (min_le_right _ _).trans (min_le_right _ _)
        linarith
  have hSc : IsPreconnected S :=
    isPreconnected_Ico.image _ (continuous_lerp p v).continuousOn
  have hpS : p ∈ S := ⟨0, ⟨le_rfl, one_pos⟩, lerp_zero p v⟩
  intro s hs
  exact subset_interior_of_isPreconnected hQ hSc hSb hpS hpi ⟨s, hs, rfl⟩

namespace TrapData

/-- Without inserted diagonal, the two cells are the whole region. -/
theorem cellL_eq_cellR (D : TrapData P) (h : ¬ D.NonAdj) : D.cellL = D.cellR := by
  ext p
  exact ⟨fun hp => ⟨hp.1, fun h' => absurd h' h⟩, fun hp => ⟨hp.1, fun h' => absurd h' h⟩⟩

section
variable (hP : P.Simple) (D : TrapData P) {h : ℝ} (h1 : D.y₁ < h) (h2 : h < D.y₂)
include hP h1 h2
/-- A point of the open left side edge is in the closure of the left cell. -/
theorem left_side_mem_closure : ((edgeX P D.i h, h) : Point) ∈ closure D.cellL :=
  D.mem_closure_cellL hP ⟨h1.le, h2.le, le_rfl, (D.isTrap.edgeX_lt hP D.free h1 h2).le⟩
    (fun hna => (D.det_side hP hna h1 h2).1)

/-- A point of the open right side edge is in the closure of the right cell. -/
theorem right_side_mem_closure : ((edgeX P D.j h, h) : Point) ∈ closure D.cellR :=
  D.mem_closure_cellR hP ⟨h1.le, h2.le, (D.isTrap.edgeX_lt hP D.free h1 h2).le, le_rfl⟩
    (fun hna => (D.det_side hP hna h1 h2).2)


end

end TrapData

/-- The points of an edge issued from its lower endpoint, just above that endpoint, are the
points of the line of the edge at heights just above. -/
theorem edge_pts_eventually {g c u : ℕ} (hNH : NonHoriz P g)
    (hseg : Chazelle.segment (P.vtx c) (P.vtx u) = P.edge g) {y₁ y₂ : ℝ}
    (hcy : (P.vtx c).2 = y₁) (h12 : y₁ < y₂) (hu2 : y₂ ≤ (P.vtx u).2) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∃ h, y₁ < h ∧ h < y₂ ∧
      lerp (P.vtx c) (P.vtx u) s = ((edgeX P g h, h) : Point) := by
  have hd : 0 < (P.vtx u).2 - y₁ := by linarith
  set s₀ := (y₂ - y₁) / ((P.vtx u).2 - y₁) with hs₀def
  have hs₀ : 0 < s₀ := div_pos (by linarith) hd
  have hs₀1 : s₀ ≤ 1 := (div_le_one hd).2 (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
  have hsd : s * ((P.vtx u).2 - y₁) < y₂ - y₁ := by
    have := (lt_div_iff₀ hd).1 hs.2; linarith
  have h2 : (lerp (P.vtx c) (P.vtx u) s).2 = y₁ + s * ((P.vtx u).2 - y₁) := by
    simp_all
  refine ⟨y₁ + s * ((P.vtx u).2 - y₁), by nlinarith [hs.1], by linarith, ?_⟩
  have hmem : lerp (P.vtx c) (P.vtx u) s ∈ P.edge g := by
    rw [← hseg]; exact lerp_mem_segment _ _ hs.1.le (by grind)
  have hx := ((mem_edge_iff_edgeX hNH).1 hmem).2
  grind

namespace TrapData

/-- **A vertex at a bottom corner.**  If the vertex `c` lies at the bottom end of the side edge `g`
(`g` is the left or the right side edge of `D`), then `c` is the lower endpoint of `g`; the other
endpoint `u` is adjacent to `c`, the only vertices on `g` are `c` and `u`, and just above `c` the
points of `g` are the points of the open side of the trapezoid. -/
theorem corner_edge (hP : P.Simple) (D : TrapData P) {c g : ℕ} (hc : c < P.n)
    (hg : g = D.i ∨ g = D.j) (hcy : (P.vtx c).2 = D.y₁) (hcx : (P.vtx c).1 = edgeX P g D.y₁) :
    ∃ u, u < P.n ∧ (u = (c + 1) % P.n ∨ c = (u + 1) % P.n) ∧
      Chazelle.segment (P.vtx c) (P.vtx u) = P.edge g ∧
      (∀ c', c' < P.n → P.vtx c' ∈ P.edge g → c' = c ∨ c' = u) ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), ∃ h, D.y₁ < h ∧ h < D.y₂ ∧
        lerp (P.vtx c) (P.vtx u) s = ((edgeX P g h, h) : Point) := by
  obtain ⟨hgn, hNH, hbot, htop⟩ :
      g < P.n ∧ NonHoriz P g ∧ edgeBot P g ≤ D.y₁ ∧ D.y₂ ≤ edgeTop P g := by
    rcases hg with rfl | rfl
    · exact ⟨D.isTrap.hi, D.isTrap.nhL, D.isTrap.botL, D.isTrap.topL⟩
    · exact ⟨D.isTrap.hj, D.isTrap.nhR, D.isTrap.botR, D.isTrap.topR⟩
  have h12 : D.y₁ < D.y₂ := D.isTrap.bot_lt.trans D.isTrap.lt_top
  have hmem : P.vtx c ∈ P.edge g :=
    (mem_edge_iff_edgeX hNH).2 ⟨⟨by simp_all, by linarith⟩,
      by simp_all⟩
  -- the height of the other endpoint
  have hu2of : ∀ u : ℕ, edgeTop P g = max (P.vtx c).2 (P.vtx u).2 → D.y₂ ≤ (P.vtx u).2 := by
    grind
  rcases (simple_vtx_mem_edge_iff hP hc hgn).1 hmem with hgc | hgc
  · -- `g = c`
    have hseg : Chazelle.segment (P.vtx c) (P.vtx ((c + 1) % P.n)) = P.edge g := by
      rw [hgc]; rfl
    have hu2 : D.y₂ ≤ (P.vtx ((c + 1) % P.n)).2 := hu2of _ (by rw [hgc]; rfl)
    refine ⟨(c + 1) % P.n, succIdx_lt P hc, Or.inl rfl, hseg, ?_,
      edge_pts_eventually hNH hseg hcy h12 hu2⟩
    intro c' hc' hmem'
    rcases (simple_vtx_mem_edge_iff hP hc' hgn).1 hmem' with h | h
    · omega
    · right; rw [← prevIdx_succ P hc', ← h, hgc]
  · -- `g = prevIdx c`
    have hseg : Chazelle.segment (P.vtx c) (P.vtx (prevIdx P c)) = P.edge g := by
      rw [hgc]; unfold Polygon.edge; rw [prevIdx_succ P hc, Geometry.segment_comm]
    have hu2 : D.y₂ ≤ (P.vtx (prevIdx P c)).2 := hu2of _ (by
      rw [hgc]; unfold edgeTop; rw [prevIdx_succ P hc, max_comm])
    refine ⟨prevIdx P c, prevIdx_lt P hc, Or.inr (prevIdx_succ P hc).symm, hseg, ?_,
      edge_pts_eventually hNH hseg hcy h12 hu2⟩
    intro c' hc' hmem'
    rcases (simple_vtx_mem_edge_iff hP hc' hgn).1 hmem' with h | h
    · omega
    · left; rw [← prevIdx_succ P hc', ← h, hgc, prevIdx_succ P hc]

end TrapData

/-- **Recognising the base.**  If `u` is adjacent in `P` to the vertex at position `m` of the
piece and the points of the edge between them near that vertex are in the closure of a set of
interior points of the piece, then `u` is a neighbour of position `m` in the piece. -/
theorem IsPiece.base_nbr (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) {m : ℕ}
    (hml : m < l.length) {u : ℕ} (hu : u < P.n)
    (hadj : u = (l.getD m 0 + 1) % P.n ∨ l.getD m 0 = (u + 1) % P.n) {S : Set Point}
    (hS : S ⊆ (subPoly P l).filled \ (subPoly P l).boundary)
    (hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp (P.vtx (l.getD m 0)) (P.vtx u) s ∈ closure S) :
    P.vtx u = (subPoly P l).vtx (prevIdx (subPoly P l) m) ∨
      P.vtx u = (subPoly P l).vtx ((m + 1) % l.length) := by
  have hpe : IsPieceEdge P (l.getD m 0) u := hadj.elim Or.inl (fun h => Or.inr (Or.inl h))
  apply hl.nbr_of_boundary hP hml hu hpe
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs hs'
  exact hl.mem_boundary_of_closure hS (hl.getD_lt hml) hu hpe
    (lerp_mem_segment _ _ hs'.1.le hs'.2.le) hs

/-- A small positive number below three positive bounds. -/
theorem exists_small_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ ε, 0 < ε ∧ ε ≤ a ∧ ε < b ∧ ε < c := by
  refine ⟨min a (min b c) / 2, by positivity, ?_, ?_, ?_⟩
  all_goals grind

section
variable (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l)
include hP hl
/-- **Initial analysis at the lowest vertex of a piece.**  Let `m` be the position of the
`ylexLT`-lowest vertex of the piece `Q = subPoly P l`.  There are an edge `e` of `P` whose only
vertices are `l.getD m 0` and `uP`, where `P.vtx uP` is a neighbour of position `m` in `Q` (the
base), and a vertex `w` which is the other neighbour of position `m` in `Q` and is in the left or
the right walk state for `e`. -/
theorem piece_initial {m : ℕ}
    (hm : IsLocMin (subPoly P l) m)
    (hmin : ∀ j < (subPoly P l).n, j ≠ m → ylexLT ((subPoly P l).vtx m) ((subPoly P l).vtx j)) :
    ∃ e uP w, e < P.n ∧ uP < P.n ∧ w < P.n ∧
      (∀ c, c < P.n → P.vtx c ∈ P.edge e → c = l.getD m 0 ∨ c = uP) ∧
      (P.vtx uP = (subPoly P l).vtx (prevIdx (subPoly P l) m) ∨
        P.vtx uP = (subPoly P l).vtx ((m + 1) % l.length)) ∧
      (P.vtx w = (subPoly P l).vtx (prevIdx (subPoly P l) m) ∨
        P.vtx w = (subPoly P l).vtx ((m + 1) % l.length)) ∧
      P.vtx w ≠ P.vtx uP ∧ (StateL P l e w ∨ StateR P l e w) := by
  set Q := subPoly P l with hQdef
  have hQ : Q.Simple := hl.simple
  have hQn : Q.n = l.length := by rw [hQdef, n_subPoly]
  have hmQ : m < Q.n := hm.1
  have hml : m < l.length := hQn ▸ hmQ
  have hmP : l.getD m 0 < P.n := hl.getD_lt hml
  set mP := l.getD m 0 with hmPdef
  set v := P.vtx mP with hvdef
  have hvm : Q.vtx m = v := IsPiece.vtx_eq hml
  have hn3 : 3 ≤ Q.n := simple_three_le hQ
  have hQn' : (m + 1) % Q.n = (m + 1) % l.length := by rw [hQn]
  have hprevl : prevIdx Q m < l.length := hQn ▸ prevIdx_lt Q hmQ
  have hnextl : (m + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
  -- the two neighbours are strictly above `v`
  have hnb : ∀ j, (j = prevIdx Q m ∨ j = (m + 1) % l.length) → ylexLT v (Q.vtx j) := by
    rintro j (rfl | rfl)
    · rw [← hvm]; exact hmin _ (prevIdx_lt Q hmQ) (prevIdx_ne Q hn3 hmQ)
    · rw [← hvm, ← hQn']
      exact hmin _ (succIdx_lt Q hmQ) (succIdx_ne Q hn3 hmQ)
  -- radii
  obtain ⟨rL, hrL, hLE⟩ := hl.locMin_lower_exterior hP hm
  obtain ⟨rB, hrB, hB⟩ := Chazelle.Existence.boundary_near_vtx hQ hmQ
  obtain ⟨rS, hrS, hSeg⟩ := exists_ball_lerp_interior hQ hmQ
  obtain ⟨rT, hrT, hTr⟩ := exists_ball_vtx_trapData hP hmP
  rw [hvm] at hLE hB hSeg
  rw [hQn'] at hB
  -- a boundary point on a horizontal ray from `v` lies on an edge of `Q` at `v`
  have hray : ∀ z : Point, z ∈ ball v rB → z ∈ Q.boundary → z.2 = v.2 → z.1 ≠ v.1 →
      ∃ j, (j = prevIdx Q m ∨ j = (m + 1) % l.length) ∧ (Q.vtx j).2 = v.2 ∧
        0 < (z.1 - v.1) * ((Q.vtx j).1 - v.1) := by
    intro z hz hzb hz2 hz1
    rcases hB z hz hzb with h | h
    · rw [Geometry.segment_comm] at h
      exact ⟨_, Or.inl rfl, ray_nbr hz2 hz1 h⟩
    · exact ⟨_, Or.inr rfl, ray_nbr hz2 hz1 h⟩
  -- the left ray from `v` is not in the piece
  have hleft : ∀ ε, 0 < ε → ε < rL → ε < rB → ((v.1 - ε, v.2) : Point) ∈ Q.filled → False := by
    intro ε hε h1 h2 hz
    have hzL : ((v.1 - ε, v.2) : Point) ∈ ball v rL := by
      rw [mem_ball_iff_abs]
      simp only [sub_self, abs_zero, sub_sub_cancel_left, abs_neg]
      exact ⟨by rw [abs_of_pos hε]; exact h1, hrL⟩
    have hzB : ((v.1 - ε, v.2) : Point) ∈ ball v rB := by
      rw [mem_ball_iff_abs]
      simp only [sub_self, abs_zero, sub_sub_cancel_left, abs_neg]
      exact ⟨by rw [abs_of_pos hε]; exact h2, hrB⟩
    have hlt : ylexLT ((v.1 - ε, v.2) : Point) v := Or.inr ⟨rfl, by simp only; linarith⟩
    have hzb : ((v.1 - ε, v.2) : Point) ∈ Q.boundary := by
      by_contra h
      exact hLE _ hzL hlt ⟨hz, h⟩
    obtain ⟨j, hj, hj2, hj1⟩ := hray _ hzB hzb rfl (by simp only; linarith)
    have hjlt : (Q.vtx j).1 < v.1 := by
      simp only [sub_sub_cancel_left] at hj1; nlinarith
    exact ylexLT_asymm (hnb j hj) (Or.inr ⟨hj2, hjlt⟩)
  -- an interior point near `v`, above `v`
  set r := min (min rL rB) (min rS rT) with hr
  have hr0 : 0 < r := lt_min (lt_min hrL hrB) (lt_min hrS hrT)
  have hrL' : r ≤ rL := (min_le_left _ _).trans (min_le_left _ _)
  have hrS' : r ≤ rS := (min_le_right _ _).trans (min_le_left _ _)
  have hrT' : r ≤ rT := (min_le_right _ _).trans (min_le_right _ _)
  have hvb : v ∈ Q.boundary := by rw [← hvm]; exact vtx_mem_boundary Q hmQ
  obtain ⟨z, hzi, hzd⟩ :=
    Metric.mem_closure_iff.1 (boundary_subset_closure_interior hQ hvb) r hr0
  have hzball : z ∈ ball v r := by rw [mem_ball, dist_comm]; exact hzd
  have hvz : ylexLT v z := by
    rcases ylexLT_trichotomy z v with h | h | h
    · exact absurd hzi (hLE z (ball_subset_ball hrL' hzball) h)
    · exact absurd (h ▸ hvb) hzi.2
    · exact h
  -- a free point of `P` above `v`, and its trapezoid
  have hUo : IsOpen (ball v r ∩ (Q.filled \ Q.boundary)) :=
    isOpen_ball.inter (isOpen_filled_sdiff_boundary hQ)
  obtain ⟨p, ⟨hpb, hpi⟩, hpf, -, hp2⟩ :=
    exists_free_of_isOpen hP hUo ⟨hzball, hzi⟩ (hl.interior_subset hzi)
  have hvp : v.2 < p.2 := by
    rcases hvz with h | ⟨h, -⟩ <;> linarith
  obtain ⟨D, -, hpD, hvD, -⟩ := hTr p (ball_subset_ball hrT' hpb) hpf
  have hmS : mP ∈ sideVtxSet P D.i D.j D.y₁ := D.mem_bot_of_lt hmP hvD hpD hvp
  have hvc : v ∈ closedTrap P D.i D.j D.y₁ D.y₂ := closure_trapSet_subset _ _ _ _ _ hvD
  have hseg : ∀ s ∈ Ico (0 : ℝ) 1,
      lerp p v s ∈ Q.filled \ Q.boundary ∧ lerp p v s ∈ D.region := by
    intro s hs
    refine ⟨hSeg p (ball_subset_ball hrS' hpb) hpi s hs, ?_⟩
    have e : lerp p v s = lerp v p (1 - s) := by
      rw [Geometry.point_ext_iff]; simp only [lerp_fst, lerp_snd]; constructor <;> ring
    rw [e]
    exact lerp_mem_trapSet hvc hpD (by linarith [hs.2]) (by linarith [hs.1])
  -- common facts
  have h12 : D.y₁ < D.y₂ := D.isTrap.bot_lt.trans D.isTrap.lt_top
  have hvy : v.2 = D.y₁ := hmS.2.1
  have hvi : edgeX P D.i D.y₁ ≤ v.1 := hmS.2.2.1
  have hvj : v.1 ≤ edgeX P D.j D.y₁ := hmS.2.2.2
  obtain ⟨hbmem, hbmax⟩ := D.isTrap.botVtx_spec hP D.free
  change D.bot ∈ sideVtxSet P D.i D.j D.y₁ at hbmem
  change ∀ k ∈ sideVtxSet P D.i D.j D.y₁, (P.vtx k).1 ≤ (P.vtx D.bot).1 at hbmax
  have hvbx : v.1 ≤ (P.vtx D.bot).1 := hbmax mP hmS
  have hfilled : ∀ {S : Set Point}, S ⊆ Q.filled \ Q.boundary → ∀ {x : Point},
      x ∈ closure S → x ∈ Q.filled :=
    fun hS _ hx => (isClosed_filled _).closure_subset (closure_mono (fun y hy => (hS hy).1) hx)
  -- the right ray from `v`, when `v` is the bottom vertex
  have hright : mP = D.bot → v.1 < edgeX P D.j D.y₁ →
      (∀ ε, 0 < ε → ε ≤ edgeX P D.j D.y₁ - v.1 → ((v.1 + ε, D.y₁) : Point) ∈ Q.filled) →
      False := by
    intro hmb hvlt hfill
    obtain ⟨ε, hε0, hε1, hεL, hεB⟩ := exists_small_pos (by linarith : 0 < edgeX P D.j D.y₁ - v.1)
      hrL hrB
    have hzf := hfill ε hε0 hε1
    
    have hzB : ((v.1 + ε, D.y₁) : Point) ∈ ball v rB := by
      rw [mem_ball_iff_abs]
      simp only [add_sub_cancel_left, ← hvy, sub_self, abs_zero]
      exact ⟨by rw [abs_of_pos hε0]; exact hεB, hrB⟩
    have hznot : ((v.1 + ε, D.y₁) : Point) ∉ Q.filled \ Q.boundary := by
      intro hzi'
      obtain ⟨ρ, hρ, hρs⟩ :=
        Metric.isOpen_iff.1 (isOpen_filled_sdiff_boundary hQ) _ hzi'
      set δ := min ρ rL / 2 with hδ
      have hδ0 : 0 < δ := by positivity
      have hδρ : δ < ρ := by have := min_le_left ρ rL; linarith
      have hδL : δ < rL := by have := min_le_right ρ rL; linarith
      have h1 : ((v.1 + ε, D.y₁ - δ) : Point) ∈ ball ((v.1 + ε, D.y₁) : Point) ρ := by
        rw [mem_ball_iff_abs]
        simp only [sub_self, abs_zero, sub_sub_cancel_left, abs_neg]
        exact ⟨hρ, by rw [abs_of_pos hδ0]; exact hδρ⟩
      have h2 : ((v.1 + ε, D.y₁ - δ) : Point) ∈ ball v rL := by
        rw [mem_ball_iff_abs]
        simp only [add_sub_cancel_left, ← hvy]
        refine ⟨by rw [abs_of_pos hε0]; exact hεL, ?_⟩
        rw [show v.2 - δ - v.2 = -δ by ring, abs_neg, abs_of_pos hδ0]; exact hδL
      exact hLE _ h2 (Or.inl (by simp only; linarith)) (hρs h1)
    have hzb : ((v.1 + ε, D.y₁) : Point) ∈ Q.boundary := by
      by_contra h
      exact hznot ⟨hzf, h⟩
    obtain ⟨j, hj, hj2, hj1⟩ := hray _ hzB hzb (by simp only; rw [hvy])
      (by simp only; linarith)
    have hja : v.1 < (Q.vtx j).1 := by
      simp only [add_sub_cancel_left] at hj1; nlinarith
    have hjl : j < l.length := by
      rcases hj with rfl | rfl
      · exact hprevl
      · exact hnextl
    have haP : l.getD j 0 < P.n := hl.getD_lt hjl
    have hjv : Q.vtx j = P.vtx (l.getD j 0) := IsPiece.vtx_eq hjl
    rw [hjv] at hj2 hja
    have hpe : IsPieceEdge P mP (l.getD j 0) := by
      rcases hj with rfl | rfl
      · have h := hl.edge_at hprevl
        have hs : (prevIdx Q m + 1) % l.length = m := by
          have := prevIdx_succ Q hmQ; rwa [hQn] at this
        rw [hs] at h
        exact h.symm
      · exact hl.edge_at hml
    have hax : (P.vtx (l.getD j 0)).1 ≤ edgeX P D.j D.y₁ := by
      by_contra hgt
      push Not at hgt
      have hs₀ : ((edgeX P D.j D.y₁, D.y₁) : Point) ∈ Chazelle.segment v (P.vtx (l.getD j 0)) :=
        horiz_mem_segment hvy (hj2.trans hvy) (min_le_of_left_le hvj)
          (le_max_of_le_right hgt.le)
      have hs₀e : ((edgeX P D.j D.y₁, D.y₁) : Point) ∈ P.edge D.j :=
        D.isTrap.mem_edgeR le_rfl h12.le rfl
      have hs₀v : ((edgeX P D.j D.y₁, D.y₁) : Point) ≠ v := fun h => by
        have := congrArg Prod.fst h; simp only at this; linarith
      have hs₀a : ((edgeX P D.j D.y₁, D.y₁) : Point) ≠ P.vtx (l.getD j 0) := fun h => by
        have := congrArg Prod.fst h; simp only at this; linarith
      rcases hpe.edge_of_mem_boundary hP hmP haP hs₀ hs₀v hs₀a D.isTrap.hj hs₀e with
        ⟨h1, h2⟩ | ⟨h1, h2⟩
      · apply D.isTrap.nhR
        show (P.vtx D.j).2 = (P.vtx ((D.j + 1) % P.n)).2
        rw [← h2, ← h1]; exact hj2.symm
      · apply D.isTrap.nhR
        show (P.vtx D.j).2 = (P.vtx ((D.j + 1) % P.n)).2
        rw [← h2, ← h1]; exact hj2
    have haS : l.getD j 0 ∈ sideVtxSet P D.i D.j D.y₁ :=
      ⟨haP, hj2.trans hvy, by linarith, hax⟩
    have := hbmax _ haS
    rw [← hmb] at this
    linarith
  -- the cell of `D` containing `p`
  have hcase : (D.NonAdj ∧ det (P.vtx D.bot) (P.vtx D.top) p < 0) ∨ p ∈ D.cellL := by
    by_cases hna : D.NonAdj
    · rcases lt_trichotomy (det (P.vtx D.bot) (P.vtx D.top) p) 0 with h | h | h
      · exact Or.inl ⟨hna, h⟩
      · exfalso
        exact hl.not_diag _ (Or.inl (D.diag_mem_trapDiagonals hna)) p
          (by rw [interior_filled hQ]; exact hpi) (D.mem_diagSeg_of_det hP hpD h)
      · exact Or.inr ⟨hpD, fun _ => h⟩
    · exact Or.inr ⟨hpD, fun h => absurd h hna⟩
  rcases hcase with ⟨hna, hneg⟩ | hpL
  · -- `p` is right of the diagonal: the base is the right side edge
    have hSR := D.cellR_subset_intQ hP hl ⟨hpD, fun _ => hneg⟩ hpi
    have hmb : mP = D.bot := by
      by_contra hne
      have hvlt : v.1 < (P.vtx D.bot).1 := lt_of_le_of_ne hvbx (fun h => hne
        (simple_vtx_inj hP hmP hbmem.1 (point_ext h (hvy.trans hbmem.2.1.symm))))
      have hdv : 0 < det (P.vtx D.bot) (P.vtx D.top) v := by
        rw [D.det_bot_top hP, hvy]; simp only [sub_self, mul_zero, zero_sub]; nlinarith
      set dp := det (P.vtx D.bot) (P.vtx D.top) p with hdp
      set dv := det (P.vtx D.bot) (P.vtx D.top) v with hdv'
      have hden : dp - dv < 0 := by linarith
      have hs0 : 0 < dp / (dp - dv) := div_pos_of_neg_of_neg hneg hden
      have hs1 : dp / (dp - dv) < 1 := (div_lt_one_of_neg hden).2 (by linarith)
      have hdet0 : det (P.vtx D.bot) (P.vtx D.top) (lerp p v (dp / (dp - dv))) = 0 := by
        rw [Geometry.det_lerp, ← hdp, ← hdv']
        have hne : dp - dv ≠ 0 := ne_of_lt hden
        calc (1 - dp / (dp - dv)) * dp + dp / (dp - dv) * dv
            = dp - dp / (dp - dv) * (dp - dv) := by ring
          _ = 0 := by rw [div_mul_cancel₀ dp hne, sub_self]
      obtain ⟨hz1, hz2⟩ := hseg _ ⟨hs0.le, hs1⟩
      exact hl.not_diag _ (Or.inl (D.diag_mem_trapDiagonals hna)) _
        (by rw [interior_filled hQ]; exact hz1) (D.mem_diagSeg_of_det hP hz2 hdet0)
    have hvcorner : v.1 = edgeX P D.j D.y₁ := by
      by_contra hne
      apply hright hmb (lt_of_le_of_ne hvj hne)
      intro ε hε hεle
      apply hfilled hSR
      refine D.mem_closure_cellR hP (D.mem_closedTrap_bot (by linarith) (by linarith))
        (fun _ => ?_)
      rw [D.det_bot_top hP, ← hmb]
      simp only [sub_self, mul_zero, zero_sub]
      nlinarith
    obtain ⟨u, hu, hadj, -, hon, hev⟩ := D.corner_edge hP hmP (Or.inr rfl) hvy hvcorner
    have hunbr := hl.base_nbr hP hml hu hadj hSR (hev.mono fun s ⟨h, h1, h2, he⟩ => by
      rw [he]; exact D.right_side_mem_closure hP h1 h2)
    have hwnbr := D.bot_top_nbr hP hl hml hmb (Or.inr hSR)
    refine ⟨D.j, u, D.top, D.isTrap.hj, hu, D.top_lt hP, hon, hunbr, hwnbr, ?_,
      Or.inr ⟨D, rfl, hSR, Or.inr (D.isTrap.topVtx_mem hP D.free)⟩⟩
    intro h
    have htu : D.top = u := simple_vtx_inj hP (D.top_lt hP) hu h
    rcases hadj with h' | h'
    · exact hna.2 (by rw [htu, h', hmb])
    · exact hna.1 (by rw [← hmb, h', htu])
  · -- `p` is in the left cell: the base is the left side edge (or the right one)
    have hSL := D.cellL_subset_intQ hP hl hpL hpi
    have hvcornerL : v.1 = edgeX P D.i D.y₁ := by
      by_contra hne
      have hvlt : edgeX P D.i D.y₁ < v.1 := lt_of_le_of_ne hvi (Ne.symm hne)
      obtain ⟨ε, hε0, hε1, hεL, hεB⟩ := exists_small_pos (by linarith : 0 < v.1 - edgeX P D.i D.y₁)
        hrL hrB
      apply hleft ε hε0 hεL hεB
      rw [hvy]
      apply hfilled hSL
      refine D.mem_closure_cellL hP (D.mem_closedTrap_bot (by linarith) (by linarith))
        (fun _ => ?_)
      rw [D.det_bot_top hP]
      simp only [sub_self, mul_zero, zero_sub]
      nlinarith
    obtain ⟨u₀, hu₀, hadj₀, hseg₀, hon₀, hev₀⟩ := D.corner_edge hP hmP (Or.inl rfl) hvy hvcornerL
    have hu₀nbr := hl.base_nbr hP hml hu₀ hadj₀ hSL (hev₀.mono fun s ⟨h, h1, h2, he⟩ => by
      rw [he]; exact D.left_side_mem_closure hP h1 h2)
    by_cases hmb : mP = D.bot
    · by_cases hna : D.NonAdj
      · have hwnbr := D.bot_top_nbr hP hl hml hmb (Or.inl hSL)
        refine ⟨D.i, u₀, D.top, D.isTrap.hi, hu₀, D.top_lt hP, hon₀, hu₀nbr, hwnbr, ?_,
          Or.inl ⟨D, rfl, hSL, Or.inr rfl⟩⟩
        intro h
        have htu : D.top = u₀ := simple_vtx_inj hP (D.top_lt hP) hu₀ h
        rcases hadj₀ with h' | h'
        · exact hna.2 (by rw [htu, h', hmb])
        · exact hna.1 (by rw [← hmb, h', htu])
      · -- no diagonal: `v` is both bottom corners
        have hvj' : v.1 = edgeX P D.j D.y₁ := by
          by_contra hne
          apply hright hmb (lt_of_le_of_ne hvj hne)
          intro ε hε hεle
          exact hfilled hSL (D.mem_closure_cellL hP
            (D.mem_closedTrap_bot (by linarith) (by linarith)) (fun h => absurd h hna))
        obtain ⟨u₁, hu₁, hadj₁, hseg₁, hon₁, hev₁⟩ :=
          D.corner_edge hP hmP (Or.inr rfl) hvy hvj'
        have hSR : D.cellR ⊆ Q.filled \ Q.boundary := by
          rw [← D.cellL_eq_cellR hna]; exact hSL
        have hu₁nbr := hl.base_nbr hP hml hu₁ hadj₁ hSR (hev₁.mono fun s ⟨h, h1, h2, he⟩ => by
          rw [he]; exact D.right_side_mem_closure hP h1 h2)
        have hvu₀ : v ≠ P.vtx u₀ := by
          have hpe : IsPieceEdge P mP u₀ := hadj₀.elim Or.inl (fun h => Or.inr (Or.inl h))
          exact hpe.vtx_ne hP hmP hu₀
        have hu01 : P.vtx u₀ ≠ P.vtx u₁ := by
          intro h
          have hne := D.isTrap.ne hP D.free.1
          have hm0 : lerp v (P.vtx u₀) (1 / 2) ∈ P.edge D.i := by
            rw [← hseg₀]; exact lerp_mem_segment _ _ (by norm_num) (by norm_num)
          have hm1 : lerp v (P.vtx u₀) (1 / 2) ∈ P.edge D.j := by
            rw [← hseg₁, ← h]; exact lerp_mem_segment _ _ (by norm_num) (by norm_num)
          have hce := (hP.2.2 D.i D.j D.isTrap.hi D.isTrap.hj hne).subset ⟨hm0, hm1⟩
          have hends : ∀ k, (k = D.i ∨ k = (D.i + 1) % P.n) → k = mP ∨ k = u₀ := by
            intro k hk
            refine hon₀ k ?_ ?_
            · rcases hk with rfl | rfl
              · exact D.isTrap.hi
              · exact succIdx_lt P D.isTrap.hi
            · rcases hk with rfl | rfl
              · exact Geometry.left_mem_segment _ _
              · exact Geometry.right_mem_segment _ _
          have hmid : ∀ k, (k = D.i ∨ k = (D.i + 1) % P.n) →
              lerp v (P.vtx u₀) (1 / 2) = P.vtx k → False := by
            intro k hk h'
            rcases hends k hk with h'' | h''
            · rw [h''] at h'; exact lerp_ne_left hvu₀ (by norm_num) h'
            · rw [h''] at h'; exact lerp_ne_right hvu₀ (by norm_num) h'
          rcases hce.1 with h' | h'
          · exact hmid _ (Or.inl rfl) h'
          · exact hmid _ (Or.inr rfl) h'
        have hwnbr := D.bot_top_nbr hP hl hml hmb (Or.inl hSL)
        have htop : P.vtx D.top = P.vtx u₀ ∨ P.vtx D.top = P.vtx u₁ := by
          rcases hu₀nbr with h0 | h0 <;> rcases hu₁nbr with h1 | h1 <;> rcases hwnbr with h2 | h2
          · exact absurd (h0.trans h1.symm) hu01
          · exact absurd (h0.trans h1.symm) hu01
          · exact Or.inl (h2.trans h0.symm)
          · exact Or.inr (h2.trans h1.symm)
          · exact Or.inr (h2.trans h1.symm)
          · exact Or.inl (h2.trans h0.symm)
          · exact absurd (h0.trans h1.symm) hu01
          · exact absurd (h0.trans h1.symm) hu01
        rcases htop with h | h
        · refine ⟨D.j, u₁, D.top, D.isTrap.hj, hu₁, D.top_lt hP, hon₁, hu₁nbr, hwnbr,
            by rw [h]; exact hu01, Or.inr ⟨D, rfl, hSR, Or.inr (D.isTrap.topVtx_mem hP D.free)⟩⟩
        · refine ⟨D.i, u₀, D.top, D.isTrap.hi, hu₀, D.top_lt hP, hon₀, hu₀nbr, hwnbr,
            by rw [h]; exact hu01.symm, Or.inl ⟨D, rfl, hSL, Or.inr rfl⟩⟩
    · obtain ⟨w, hwS, hwx, hwnbr⟩ := D.bot_right_nbr hP hl hml rfl hmS hmb hSL
      refine ⟨D.i, u₀, w, D.isTrap.hi, hu₀, hwS.1, hon₀, hu₀nbr, hwnbr, ?_,
        Or.inl ⟨D, rfl, hSL, Or.inl hwS⟩⟩
      intro h
      have hwe : P.vtx w ∈ P.edge D.i := by
        rw [h, ← hseg₀]; exact Geometry.right_mem_segment _ _
      have hx := ((mem_edge_iff_edgeX D.isTrap.nhL).1 hwe).2
      rw [hwS.2.1] at hx
      linarith

/-! ### The walk -/

/-- **The walk.**  Let `f` enumerate positions of the piece such that the two neighbours of
`f (k + 1)` are `f k` and `f (k + 2)`, and let `St` be a predicate on vertices of `P` such that
every vertex `f k` (`1 ≤ k ≤ n - 2`) satisfying `St` has a neighbour, strictly `ylexLT`-above it,
satisfying `St`.  If `f 1` satisfies `St` and is above `f 0`, the vertices `f 0, f 1, …, f (n-1)`
are strictly increasing. -/
theorem walk_chain (St : ℕ → Prop)
    (f : ℕ → ℕ) (hf : ∀ k, f k < l.length)
    (hnb : ∀ k, k + 2 < l.length →
      ((subPoly P l).vtx (f k) = (subPoly P l).vtx (prevIdx (subPoly P l) (f (k + 1))) ∧
        (subPoly P l).vtx (f (k + 2)) = (subPoly P l).vtx ((f (k + 1) + 1) % l.length)) ∨
      ((subPoly P l).vtx (f k) = (subPoly P l).vtx ((f (k + 1) + 1) % l.length) ∧
        (subPoly P l).vtx (f (k + 2)) = (subPoly P l).vtx (prevIdx (subPoly P l) (f (k + 1)))))
    (htr : ∀ k, 1 ≤ k → k + 2 ≤ l.length → St (l.getD (f k) 0) →
      ∃ w, w < P.n ∧ St w ∧ ylexLT (P.vtx (l.getD (f k) 0)) (P.vtx w) ∧
        (P.vtx w = (subPoly P l).vtx (prevIdx (subPoly P l) (f k)) ∨
          P.vtx w = (subPoly P l).vtx ((f k + 1) % l.length)))
    (h1 : St (l.getD (f 1) 0))
    (h01 : ylexLT ((subPoly P l).vtx (f 0)) ((subPoly P l).vtx (f 1))) :
    ∀ k, k + 1 < l.length →
      ylexLT ((subPoly P l).vtx (f k)) ((subPoly P l).vtx (f (k + 1))) := by
  set Q := subPoly P l with hQdef
  have main : ∀ k, 1 ≤ k → k < l.length →
      St (l.getD (f k) 0) ∧ ylexLT (Q.vtx (f (k - 1))) (Q.vtx (f k)) := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      intro _ hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · ram_grind
      · obtain ⟨hSt, hlt⟩ := ih hkpos (by omega)
        obtain ⟨w, hw, hStw, hcw, hnbw⟩ := htr k hkpos (by omega) hSt
        have hvk : Q.vtx (f k) = P.vtx (l.getD (f k) 0) := IsPiece.vtx_eq (hf k)
        rw [← hvk] at hcw
        have hn := hnb (k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega, show k - 1 + 2 = k + 1 by omega] at hn
        have hw' : P.vtx w = Q.vtx (f (k + 1)) := by
          rcases hn with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases hnbw with h | h
          · have e := h.trans ha.symm
            rw [e] at hcw
            exact absurd hcw (ylexLT_asymm hlt)
          · rw [hb, h]
          · rw [hb, h]
          · have e := h.trans ha.symm
            rw [e] at hcw
            exact absurd hcw (ylexLT_asymm hlt)
        refine ⟨?_, ?_⟩
        · have hwe : w = l.getD (f (k + 1)) 0 :=
            simple_vtx_inj hP hw (hl.getD_lt (hf _)) (hw'.trans (IsPiece.vtx_eq (hf _)))
          grind
        grind
  grind


end

/-- The predecessor of a residue. -/
theorem prevIdx_mod_add_sub {Q : Polygon} {N : ℕ} (hQN : Q.n = N) (hN : 0 < N) (x : ℕ) :
    prevIdx Q (x % N) = (x + (N - 1)) % N := by
  unfold prevIdx
  rw [hQN, show x % N + N - 1 = x % N + (N - 1) by omega, Nat.mod_add_mod]

section
variable (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l)
include hP hl
/-- **Monotonicity from the walk.**  Let `m` be the position of the lowest vertex of the piece,
`uP` one neighbour of position `m` and `w` the other one, and `St` a walk predicate satisfied by
`w` and propagated upwards from every vertex other than `l.getD m 0` and `uP`.  Then the piece is
a monotone mountain (in one of the two orientations). -/
theorem mono_of_walk {m : ℕ}
    (hml : m < l.length)
    (hmin : ∀ j < l.length, j ≠ m → ylexLT ((subPoly P l).vtx m) ((subPoly P l).vtx j))
    (St : ℕ → Prop) {uP w : ℕ} (huP : uP < P.n) (hw : w < P.n)
    (hstep : ∀ k, k < l.length → l.getD k 0 ≠ l.getD m 0 → l.getD k 0 ≠ uP →
      St (l.getD k 0) → ∃ w', w' < P.n ∧ St w' ∧ ylexLT (P.vtx (l.getD k 0)) (P.vtx w') ∧
        (P.vtx w' = (subPoly P l).vtx (prevIdx (subPoly P l) k) ∨
          P.vtx w' = (subPoly P l).vtx ((k + 1) % l.length)))
    (hu : P.vtx uP = (subPoly P l).vtx (prevIdx (subPoly P l) m) ∨
      P.vtx uP = (subPoly P l).vtx ((m + 1) % l.length))
    (hwn : P.vtx w = (subPoly P l).vtx (prevIdx (subPoly P l) m) ∨
      P.vtx w = (subPoly P l).vtx ((m + 1) % l.length))
    (hwu : P.vtx w ≠ P.vtx uP) (hSt : St w) :
    ∃ a < l.length, IsMonoAt (subPoly P l) a := by
  set Q := subPoly P l with hQdef
  set N := l.length with hNdef
  have hQ : Q.Simple := hl.simple
  have hQn : Q.n = N := by grind [n_subPoly]
  have hN3 : 3 ≤ N := hQn ▸ simple_three_le hQ
  have hN0 : 0 < N := by omega
  have hmQ : m < Q.n := hQn ▸ hml
  have hprevN : prevIdx Q m = (m + (N - 1)) % N := by
    unfold prevIdx; rw [hQn, show m + N - 1 = m + (N - 1) by omega]
  -- vertices at positions
  have hvtx : ∀ {k}, k < N → Q.vtx k = P.vtx (l.getD k 0) := fun hk => IsPiece.vtx_eq hk
  have hidx : ∀ {k c}, k < N → c < P.n → P.vtx c = Q.vtx k → c = l.getD k 0 :=
    fun hk hc h => simple_vtx_inj hP hc (hl.getD_lt hk) (h.trans (hvtx hk))
  rcases hu with hu | hu
  · -- forward walk: the base is the edge from position `m - 1` to position `m`
    have hwn' : P.vtx w = Q.vtx ((m + 1) % N) := by
      grind
    set f : ℕ → ℕ := fun k => (m + k) % N with hfdef
    have hf : ∀ k, f k < N := fun k => Nat.mod_lt _ hN0
    have hfinj : ∀ k k', k < N → k' < N → f k = f k' → k = k' := fun k k' hk hk' h =>
      Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' m h) hk hk'
    have hf0 : f 0 = m := by simp only [hfdef, add_zero]; exact Nat.mod_eq_of_lt hml
    have hfN : f (N - 1) = prevIdx Q m := by rw [hprevN]
    have chain := walk_chain hP hl St f hf
      (fun k _ => Or.inl ⟨by
          congr 1
          rw [show f (k + 1) = (m + k + 1) % N by grind,
            prevIdx_mod_add_sub hQn hN0, show m + k + 1 + (N - 1) = m + k + N by omega,
            Nat.add_mod_right],
        by
          grind⟩)
      (fun k hk1 hk2 hSk => by
        refine hstep (f k) (hf k) (fun h => ?_) (fun h => ?_) hSk
        · have := hfinj k 0 (by omega) (by omega) ((hl.getD_inj (hf k) hml h).trans hf0.symm)
          omega
        · have hu' := hidx (prevIdx_lt Q hmQ |>.trans_eq hQn) huP hu
          rw [← h] at hu'
          have := hfinj k (N - 1) (by omega) (by omega)
            ((hl.getD_inj (hf k) (prevIdx_lt Q hmQ |>.trans_eq hQn) hu').trans hfN.symm)
          omega)
      (by
        have := hidx (hf 1) hw (by rw [hwn']); grind)
      (by
        rw [hf0]
        refine hmin _ (hf 1) (fun h => ?_)
        have := hfinj 1 0 (by omega) (by omega) (h.trans hf0.symm)
        omega)
    refine ⟨prevIdx Q m, prevIdx_lt Q hmQ |>.trans_eq hQn, hQ, prevIdx_lt Q hmQ, Or.inl ?_⟩
    intro p hp
    have hpos : ∀ q, (prevIdx Q m + 1 + q) % Q.n = f q := by
      intro q
      rw [← Nat.mod_add_mod, prevIdx_succ Q hmQ, hQn]
    rw [hpos, hpos]
    exact chain p (by omega)
  · -- backward walk: the base is the edge from position `m` to position `m + 1`
    
    set f : ℕ → ℕ := fun k => (m + (N - 1) * k) % N with hfdef
    have hf : ∀ k, f k < N := fun k => Nat.mod_lt _ hN0
    have hkey : ∀ k, (f k + k) % N = m % N := by
      intro k
      simp only [hfdef]
      rw [Nat.mod_add_mod, show m + (N - 1) * k + k = m + N * k by
        rw [add_assoc, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)],
        Nat.add_mul_mod_self_left]
    have hfeq : ∀ k x, x < N → (x + k) % N = m % N → f k = x := by
      intro k x hx h
      have h1 : f k + k ≡ x + k [MOD N] := (hkey k).trans h.symm
      exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' k h1) (hf k) hx
    have hfinj : ∀ k k', k < N → k' < N → f k = f k' → k = k' := by
      intro k k' hk hk' h
      have h1 : f k + k ≡ f k + k' [MOD N] := by
        show (f k + k) % N = (f k + k') % N
        rw [hkey k, h, hkey k']
      exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' _ h1) hk hk'
    have hf0 : f 0 = m := by simp only [hfdef, mul_zero, add_zero]; exact Nat.mod_eq_of_lt hml
    have hfN : f (N - 1) = (m + 1) % N := by
      apply hfeq _ _ (Nat.mod_lt _ hN0)
      rw [Nat.mod_add_mod, show m + 1 + (N - 1) = m + N by omega, Nat.add_mod_right]
    have hnext : ∀ k, (f (k + 1) + 1) % N = f k := by
      intro k
      symm
      apply hfeq _ _ (Nat.mod_lt _ hN0)
      rw [Nat.mod_add_mod, show f (k + 1) + 1 + k = f (k + 1) + (k + 1) by ring, hkey]
    have hprev : ∀ k, prevIdx Q (f (k + 1)) = f (k + 2) := by
      intro k
      rw [show f (k + 1) = (f (k + 1)) % N from (Nat.mod_eq_of_lt (hf _)).symm,
        prevIdx_mod_add_sub hQn hN0]
      grind
    have chain := walk_chain hP hl St f hf
      (fun k _ => Or.inr ⟨by rw [hnext], by rw [hprev]⟩)
      (fun k hk1 hk2 hSk => by
        refine hstep (f k) (hf k) (fun h => ?_) (fun h => ?_) hSk
        · have := hfinj k 0 (by omega) (by omega) ((hl.getD_inj (hf k) hml h).trans hf0.symm)
          omega
        · have hnl : (m + 1) % N < N := Nat.mod_lt _ hN0
          have hu' := hidx hnl huP hu
          rw [← h] at hu'
          have := hfinj k (N - 1) (by omega) (by omega)
            ((hl.getD_inj (hf k) hnl hu').trans hfN.symm)
          omega)
      (by
        
        have := hidx (hf 1) hw (by grind); grind)
      (by
        rw [hf0]
        refine hmin _ (hf 1) (fun h => ?_)
        have := hfinj 1 0 (by omega) (by omega) (h.trans hf0.symm)
        omega)
    refine ⟨m, hml, hQ, hmQ, Or.inr ?_⟩
    intro p hp
    rw [hQn] at hp ⊢
    have e1 : (m + 1 + (p + 1)) % N = f (N - 2 - p) := by
      symm
      apply hfeq _ _ (Nat.mod_lt _ hN0)
      rw [Nat.mod_add_mod, show m + 1 + (p + 1) + (N - 2 - p) = m + N by omega, Nat.add_mod_right]
    have e2 : (m + 1 + p) % N = f (N - 2 - p + 1) := by
      symm
      apply hfeq _ _ (Nat.mod_lt _ hN0)
      rw [Nat.mod_add_mod, show m + 1 + p + (N - 2 - p + 1) = m + N by omega, Nat.add_mod_right]
    rw [e1, e2]
    exact chain _ (by omega)

/-- **The mountain decomposition theorem.**  Every piece of the subdivision of a simple polygon
`P` by the inserted diagonals `allDiagonals P` is a monotone mountain: for some position `a`,
the vertices of the piece read cyclically from position `a + 1` to position `a` are strictly
`ylexLT`-increasing or strictly `ylexLT`-decreasing (so the edge `a` of the piece is its base). -/
theorem piece_isMonoAt :
    ∃ a < l.length, IsMonoAt (subPoly P l) a := by
  set Q := subPoly P l with hQdef
  have hQ : Q.Simple := hl.simple
  have hQn : Q.n = l.length := by simp_all
  obtain ⟨m, hm, hmin⟩ := exists_isLocMin hQ
  have hml : m < l.length := hQn ▸ hm.1
  have hmin' : ∀ j < l.length, j ≠ m → ylexLT (Q.vtx m) (Q.vtx j) :=
    fun j hj hjm => hmin j (hQn ▸ hj) hjm
  obtain ⟨e, uP, w, he, huP, hw, hon, hu, hwn, hwu, hst⟩ := piece_initial hP hl hm hmin
  have hnot : ∀ c, c < P.n → c ≠ l.getD m 0 → c ≠ uP → P.vtx c ∉ P.edge e := by
    grind
  rcases hst with hst | hst
  · exact mono_of_walk hP hl hml hmin' (StateL P l e) huP hw
      (fun k hk h1 h2 hSk => StateL.step hP hl he hk rfl hSk
        (hnot _ (hl.getD_lt hk) h1 h2)) hu hwn hwu hst
  · exact mono_of_walk hP hl hml hmin' (StateR P l e) huP hw
      (fun k hk h1 h2 hSk => StateR.step hP hl he hk rfl hSk
        (hnot _ (hl.getD_lt hk) h1 h2)) hu hwn hwu hst

/-! ### Reversing the orientation of a piece -/


end

/-- The index of the edge of `Q` carrying edge `k` of the reversed polygon (`n` vertices). -/
def revEdge (n k : ℕ) : ℕ := if k + 1 < n then n - 2 - k else n - 1

section
variable {n k : ℕ} (hk : k < n)
include hk
/-- `revEdge n` maps indices below `n` to indices below `n`. -/
theorem revEdge_lt : revEdge n k < n := by
  core_grind

/-- `revEdge n` is an involution on indices below `n`. -/
theorem revEdge_revEdge : revEdge n (revEdge n k) = k := by
  core_grind


end

section Reverse

variable {Q R : Polygon}

section
variable (hn : R.n = Q.n) (hv : ∀ k < Q.n, R.vtx k = Q.vtx (Q.n - 1 - k))
include hn hv
section
variable {k : ℕ} (hk : k < Q.n)
include k hk
/-- The endpoints of edge `k` of a reversed polygon `R` (`R.vtx k = Q.vtx (n - 1 - k)`) are the
endpoints of edge `revEdge n k` of `Q`, in the opposite order. -/
theorem rev_endpoints :
    R.vtx k = Q.vtx ((revEdge Q.n k + 1) % Q.n) ∧
      R.vtx ((k + 1) % R.n) = Q.vtx (revEdge Q.n k) := by
  rw [hn]
  unfold revEdge
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (show Q.n - 2 - k + 1 < Q.n by omega), Nat.mod_eq_of_lt h, hv k hk,
      hv (k + 1) h]
    grind
  · have hk' : k = Q.n - 1 := by omega
    simp_all +arith

/-- Edge `k` of the reversed polygon is edge `revEdge n k` of `Q`. -/
theorem rev_edge : R.edge k = Q.edge (revEdge Q.n k) := by
  obtain ⟨e1, e2⟩ := rev_endpoints hn hv hk
  simp_all [Polygon.edge, Geometry.segment_comm]


end

/-- **A reversed polygon has the same boundary.** -/
theorem rev_boundary :
    R.boundary = Q.boundary := by
  ext p
  constructor
  · rintro ⟨k, hk, hp⟩
    rw [hn] at hk
    exact ⟨_, revEdge_lt hk, by rw [← rev_edge hn hv hk]; exact hp⟩
  · rintro ⟨j, hj, hp⟩
    refine ⟨revEdge Q.n j, by rw [hn]; exact revEdge_lt hj, ?_⟩
    rw [rev_edge hn hv (revEdge_lt hj), revEdge_revEdge hj]
    exact hp

/-- **A reversed polygon has the same filled region.** -/
theorem rev_filled :
    R.filled = Q.filled := by
  unfold Polygon.filled
  rw [rev_boundary hn hv]

/-- **A reversed simple polygon is simple.** -/
theorem rev_simple
    (hQ : Q.Simple) : R.Simple := by
  refine ⟨hn ▸ hQ.1, fun i j hi hj h => ?_, fun i j hi hj hij => ?_⟩
  · rw [hn] at hi hj
    rw [hv i hi, hv j hj] at h
    have := hQ.2.1 _ _ (by omega) (by omega) h
    omega
  · rw [hn] at hi hj
    rw [rev_edge hn hv hi, rev_edge hn hv hj]
    have hne : revEdge Q.n i ≠ revEdge Q.n j := fun h => hij (by
      have := congrArg (revEdge Q.n) h
      rwa [revEdge_revEdge hi, revEdge_revEdge hj] at this)
    rw [hQ.2.2 _ _ (revEdge_lt hi) (revEdge_lt hj) hne]
    obtain ⟨a1, a2⟩ := rev_endpoints hn hv hi
    obtain ⟨b1, b2⟩ := rev_endpoints hn hv hj
    grind [Polygon.commonEndpoints, Set.mem_ofPred_eq]


end

/-- Two residues adding up to `n - 1` modulo `n`. -/
theorem eq_sub_of_add_mod {N u v : ℕ} (hu : u < N) (hv : v < N)
    (h : (u + v) % N = (N - 1) % N) : u = N - 1 - v := by
  rw [Nat.mod_eq_of_lt (show N - 1 < N by omega)] at h
  rcases Nat.lt_or_ge (u + v) N with h' | h'
  · rw [Nat.mod_eq_of_lt h'] at h; omega
  · rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)] at h; omega

/-- **A decreasing chain becomes increasing after reversal.** -/
theorem rev_chainInc (hn : R.n = Q.n) (hv : ∀ k < Q.n, R.vtx k = Q.vtx (Q.n - 1 - k))
    (h3 : 3 ≤ Q.n) {a : ℕ} (ha : a < Q.n) (h : ChainDec Q a) :
    ChainInc R ((2 * Q.n - 2 - a) % Q.n) := by
  set N := Q.n with hN
  intro p hp
  rw [hn] at hp ⊢
  have hN0 : 0 < N := by omega
  have hx1 : (((2 * N - 2 - a) % N) + 1 + p) % N < N := Nat.mod_lt _ hN0
  have hx2 : (((2 * N - 2 - a) % N) + 1 + (p + 1)) % N < N := Nat.mod_lt _ hN0
  rw [hv _ hx1, hv _ hx2]
  have key : ∀ q, q + 1 ≤ N →
      N - 1 - (((2 * N - 2 - a) % N) + 1 + q) % N = (a + 1 + (N - 1 - q)) % N := by
    intro q hq
    symm
    apply eq_sub_of_add_mod (Nat.mod_lt _ hN0) (Nat.mod_lt _ hN0)
    have e1 : ((a + 1 + (N - 1 - q)) % N + ((2 * N - 2 - a) % N + 1 + q) % N) % N =
        (a + 1 + (N - 1 - q) + (2 * N - 2 - a + 1 + q)) % N :=
      (Nat.mod_modEq (a + 1 + (N - 1 - q)) N).add ((Nat.mod_modEq _ N).trans
        (((Nat.mod_modEq (2 * N - 2 - a) N).add_right 1).add_right q))
    rw [e1, show a + 1 + (N - 1 - q) + (2 * N - 2 - a + 1 + q) = N - 1 + N * 2 by omega,
      Nat.add_mul_mod_self_left]
  rw [key p (by omega), key (p + 1) (by omega)]
  have := h (N - 2 - p) (by omega)
  rw [show N - 2 - p + 1 = N - 1 - p by omega] at this
  grind

end Reverse

/-- The reversed piece: its vertices are those of the piece in the opposite order. -/
theorem vtx_subPoly_reverse (P : Polygon) (l : List ℕ) {k : ℕ} (hk : k < l.length) :
    (subPoly P l.reverse).vtx k = (subPoly P l).vtx (l.length - 1 - k) := by
  rw [vtx_subPoly_getD P l.reverse (by simp_all), getD_reverse l hk,
    vtx_subPoly_getD P l (by omega)]

/-- The reversed piece has the same number of vertices. -/
theorem n_subPoly_reverse (P : Polygon) (l : List ℕ) :
    (subPoly P l.reverse).n = (subPoly P l).n := by
  simp_all

/-- **The reversed piece has the same filled region.** -/
theorem filled_subPoly_reverse (P : Polygon) (l : List ℕ) :
    (subPoly P l.reverse).filled = (subPoly P l).filled :=
  rev_filled (n_subPoly_reverse P l) (fun k hk => by
    rw [n_subPoly] at hk ⊢; exact vtx_subPoly_reverse P l hk)

/-- **The reversed piece is simple.** -/
theorem simple_subPoly_reverse {l : List ℕ} (h : (subPoly P l).Simple) :
    (subPoly P l.reverse).Simple :=
  rev_simple (n_subPoly_reverse P l) (fun k hk => by
    rw [n_subPoly] at hk ⊢; exact vtx_subPoly_reverse P l hk) h

section
variable (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l)
include hP hl
/-- **The mountain decomposition theorem, oriented form.**  Every piece is a monotone mountain
with increasing chain (`IsMountainAt`, base = edge `a`), either as listed or after reversing
its vertex list. -/
theorem piece_isMountainAt :
    ∃ a < l.length, IsMountainAt (subPoly P l) a ∨ IsMountainAt (subPoly P l.reverse) a := by
  obtain ⟨a, ha, hQ, haQ, hc⟩ := piece_isMonoAt hP hl
  rcases hc with hc | hc
  · exact ⟨a, ha, Or.inl ⟨hQ, haQ, hc⟩⟩
  · have hn := n_subPoly_reverse P l
    have hv : ∀ k < (subPoly P l).n,
        (subPoly P l.reverse).vtx k = (subPoly P l).vtx ((subPoly P l).n - 1 - k) := by
      intro k hk; rw [n_subPoly] at hk ⊢; exact vtx_subPoly_reverse P l hk
    have hlen : (subPoly P l).n = l.length := n_subPoly P l
    refine ⟨(2 * l.length - 2 - a) % l.length, Nat.mod_lt _ (by omega), Or.inr
      ⟨simple_subPoly_reverse hQ, by rw [hn, hlen]; exact Nat.mod_lt _ (by omega), ?_⟩⟩
    have := rev_chainInc hn hv hQ.1 haQ hc
    grind

/-- **The mountain decomposition theorem, in the form used by the stack algorithm.**  Every piece
of the subdivision of a simple polygon by `allDiagonals P` is, after rotation, a monotone
mountain in the sense of `Chazelle.Mountain.IsMountain` (vertices listed in strictly increasing
`ylexLT` order, base = last edge), either with its vertex list as given or reversed.  The
reversed piece has the same boundary and filled region (`boundary_subPoly_reverse`,
`filled_subPoly_reverse`). -/
theorem piece_isMountain :
    ∃ s, IsMountain ((subPoly P l).rotate s) ∨ IsMountain ((subPoly P l.reverse).rotate s) := by
  obtain ⟨a, ha, h | h⟩ := piece_isMountainAt hP hl
  · have haQ : a < (subPoly P l).n := by simp_all
    exact ⟨(a + 1) % (subPoly P l).n, Or.inl ((isMountainAt_iff haQ).1 h)⟩
  · have haQ : a < (subPoly P l.reverse).n := by
      simp_all
    refine ⟨(a + 1) % (subPoly P l.reverse).n, Or.inr ((isMountainAt_iff haQ).1 h)⟩


end

end

end Chazelle.Mountain
