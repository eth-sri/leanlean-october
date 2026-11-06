module

public meta import Chazelle.Arithmetic

public import Chazelle.Mountain.Pieces

/-!
# Pieces of the mountain decomposition: cells, gaps and boundary recognition

Infrastructure for the proof that every piece of the subdivision of a simple polygon `P` by
`allDiagonals P` is a monotone mountain (`Chazelle.Mountain.PiecesMain`).

Throughout, `l` is a piece (`IsPiece P l`) and `Q = subPoly P l`.

* **Piece segments** (`IsPieceEdge`): a vertex of `P` on a piece segment is one of its endpoints
  (`IsPieceEdge.vtx_eq_of_mem`); two piece segments issued from a common vertex and sharing a
  further point coincide (`IsPieceEdge.eq_of_mem_of_mem`).
* **Boundary recognition** (`IsPiece.nbr_of_boundary`): if the points of a piece segment
  `[P.vtx c, P.vtx w]` issued from the vertex `c` of `Q` (at position `k`) lie on the boundary of
  `Q` near `P.vtx c`, then `P.vtx w` is one of the two neighbours of position `k` in `Q`.
* **Cells** (`TrapData.cellL`, `TrapData.cellR`): the parts of a trapezoid region to the left and
  to the right of its inserted diagonal (the whole region if no diagonal is inserted).  A cell
  meets no boundary point of `Q` (`TrapData.cellL_not_mem_boundaryQ`), so a cell containing an
  interior point of `Q` lies in the interior of `Q` (`TrapData.cellL_subset_intQ`).  The closure
  of a cell contains the points of the closed trapezoid on its side of the diagonal
  (`TrapData.mem_closure_cellL`, …).
* **Gaps** (`TrapData.gap_top`): a portion of the open top side of a trapezoid, free of
  vertices and ending at an interior point of a non-horizontal edge, carries no point of the
  boundary of `P` and no point of an inserted diagonal.
* **The trapezoid above a gap** (`exists_trapData_above`): above an open horizontal segment of
  interior chord points there is a trapezoid whose closed bottom side contains the segment;
  `TrapData.i_eq_of_openEdgePt`, `TrapData.j_eq_of_openEdgePt` identify its side edges.
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

/-! ### Piece segments -/

/-- Piece edges are symmetric. -/
theorem IsPieceEdge.symm {x y : ℕ} (h : IsPieceEdge P x y) : IsPieceEdge P y x := by
  core_grind

section
variable (hP : P.Simple) {x y : ℕ} (hx : x < P.n) (hy : y < P.n) (h : IsPieceEdge P x y)
include hP hx hy h
/-- The two endpoints of a piece edge are distinct. -/
theorem IsPieceEdge.ne : x ≠ y := by
  have hn := simple_three_le hP
  rcases h with h | h | h | h
  · intro e; subst e; exact succIdx_ne P hn hx h.symm
  · intro e; subst e; exact succIdx_ne P hn hy h.symm
  · exact (allDiagonals_lt hP h).2.2
  · exact fun e => (allDiagonals_lt hP h).2.2 e.symm

/-- The two endpoint points of a piece edge are distinct. -/
theorem IsPieceEdge.vtx_ne : P.vtx x ≠ P.vtx y :=
  fun e => h.ne hP hx hy (simple_vtx_inj hP hx hy e)


end

section
variable (hP : P.Simple)
include hP
/-- An allowed diagonal: points of its segment other than its endpoints avoid the boundary. -/
theorem allDiagonals_not_mem_boundary {d : ℕ × ℕ} (hd : d ∈ allDiagonals P)
    {p : Point} (hp : p ∈ diagSeg P d) (h1 : p ≠ P.vtx d.1) (h2 : p ≠ P.vtx d.2) :
    p ∉ P.boundary := by
  obtain ⟨s, L, hD, hs, hsL, -⟩ := allDiagonals_isDiagonal hP hd
  have := hD.2.2 p (by aesop) (by simp_all) (by simp_all)
  exact this

/-- **A point of a piece segment lying on the boundary of `P` and different from its endpoints
lies on the edge of `P` that the segment is.** -/
theorem IsPieceEdge.edge_of_mem_boundary {x y : ℕ} (hx : x < P.n) (hy : y < P.n)
    (h : IsPieceEdge P x y) {q : Point} (hq : q ∈ Chazelle.segment (P.vtx x) (P.vtx y))
    (hqx : q ≠ P.vtx x) (hqy : q ≠ P.vtx y) {g : ℕ} (hg : g < P.n) (hqg : q ∈ P.edge g) :
    (x = g ∧ y = (g + 1) % P.n) ∨ (y = g ∧ x = (g + 1) % P.n) := by
  rcases h with h | h | h | h
  · -- the segment is edge `x`
    by_cases hxg : x = g
    · simp_all
    · exfalso
      have hq' : q ∈ P.edge x := by grind [Polygon.edge]
      have := (hP.2.2 x g hx hg hxg).subset ⟨hq', hqg⟩
      rcases this.1 with e | e
      all_goals simp_all
  · -- the segment is edge `y`
    by_cases hyg : y = g
    · simp_all
    · exfalso
      have hq' : q ∈ P.edge y := by
        grind [Polygon.edge, Geometry.segment_comm]
      have := (hP.2.2 y g hy hg hyg).subset ⟨hq', hqg⟩
      rcases this.1 with e | e
      all_goals simp_all
  · exact absurd ⟨g, hg, hqg⟩ (allDiagonals_not_mem_boundary hP h hq hqx hqy)
  · exact absurd ⟨g, hg, hqg⟩ (allDiagonals_not_mem_boundary hP h
      (by grind [diagSeg, Geometry.segment_comm]) hqy hqx)

/-- **A vertex of `P` on a piece segment is one of its endpoints.** -/
theorem IsPieceEdge.vtx_eq_of_mem {x y z : ℕ} (hx : x < P.n) (hy : y < P.n)
    (hz : z < P.n) (h : IsPieceEdge P x y)
    (hmem : P.vtx z ∈ Chazelle.segment (P.vtx x) (P.vtx y)) : z = x ∨ z = y := by
  by_contra hcon
  push Not at hcon
  have h1 : P.vtx z ≠ P.vtx x := fun e => hcon.1 (simple_vtx_inj hP hz hx e)
  have h2 : P.vtx z ≠ P.vtx y := fun e => hcon.2 (simple_vtx_inj hP hz hy e)
  rcases h.edge_of_mem_boundary hP hx hy hmem h1 h2 hz (Geometry.left_mem_segment _ _) with
    ⟨rfl, -⟩ | ⟨rfl, -⟩
  all_goals omega

/-- **Two piece segments issued from a common vertex and sharing a further point coincide.** -/
theorem IsPieceEdge.eq_of_mem_of_mem {c w w' : ℕ} (hc : c < P.n) (hw : w < P.n)
    (hw' : w' < P.n) (h : IsPieceEdge P c w) (h' : IsPieceEdge P c w') {x : Point}
    (hx : x ∈ Chazelle.segment (P.vtx c) (P.vtx w)) (hx' : x ∈ Chazelle.segment (P.vtx c) (P.vtx w'))
    (hxc : x ≠ P.vtx c) : w = w' := by
  obtain ⟨s, hs0, hs1, rfl⟩ := hx
  obtain ⟨s', hs0', hs1', he⟩ := hx'
  set a := P.vtx c
  set b := P.vtx w
  set b' := P.vtx w'
  
  
  have hs : s ≠ 0 := by
    grind
  have hs' : s' ≠ 0 := by
    grind
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
  have hspos' : 0 < s' := lt_of_le_of_ne hs0' (Ne.symm hs')
  rcases le_total s' s with hle | hle
  · -- `w` lies on the segment `[c, w']`
    have hmem : P.vtx w ∈ Chazelle.segment a b' := by
      refine ⟨s' / s, div_nonneg hspos'.le hspos.le, (div_le_one hspos).2 hle, ?_⟩
      grind
    rcases h'.vtx_eq_of_mem hP hc hw' hw hmem with e | e
    all_goals grind
  · have hmem : P.vtx w' ∈ Chazelle.segment a b := by
      refine ⟨s / s', div_nonneg hspos.le hspos'.le, (div_le_one hspos').2 hle, ?_⟩
      grind
    rcases h.vtx_eq_of_mem hP hc hw hw' hmem with e | e
    all_goals grind

/-! ### Pieces: indices and boundary -/


end

section
variable {l : List ℕ}
/-- The indices of a piece are vertices of `P`. -/
theorem IsPiece.getD_lt (hl : IsPiece P l) {k : ℕ} (hk : k < l.length) :
    l.getD k 0 < P.n := by
  apply hl.lt
  simp_all

/-- The vertex at position `k` of a piece is the vertex `l.getD k 0` of `P`. -/
theorem IsPiece.vtx_eq {k : ℕ} (hk : k < l.length) :
    (subPoly P l).vtx k = P.vtx (l.getD k 0) :=
  vtx_subPoly_getD P l hk


end

section
variable {l : List ℕ} (hl : IsPiece P l)
include hl
/-- The cyclic edge of a piece at position `k` is a piece edge. -/
theorem IsPiece.edge_at {k : ℕ} (hk : k < l.length) :
    IsPieceEdge P (l.getD k 0) (l.getD ((k + 1) % l.length) 0) :=
  hl.edges k hk

/-- Distinct positions of a piece carry distinct vertices of `P`. -/
theorem IsPiece.getD_inj {k k' : ℕ} (hk : k < l.length)
    (hk' : k' < l.length) (h : l.getD k 0 = l.getD k' 0) : k = k' := by
  core_grind

/-- A boundary point of a piece lies on the boundary of `P` or on an inserted diagonal. -/
theorem IsPiece.mem_boundary_cases {p : Point}
    (hp : p ∈ (subPoly P l).boundary) :
    p ∈ P.boundary ∨ ∃ d ∈ allDiagonals P, p ∈ diagSeg P d := by
  obtain ⟨k, hk, hpk⟩ := hp
  rw [n_subPoly] at hk
  have hk1 : (k + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
  have he : (subPoly P l).edge k =
      Chazelle.segment (P.vtx (l.getD k 0)) (P.vtx (l.getD ((k + 1) % l.length) 0)) := by
    unfold Polygon.edge
    rw [n_subPoly, IsPiece.vtx_eq hk, IsPiece.vtx_eq hk1]
  rw [he] at hpk
  rcases (hl.edge_at hk).segment_cases (hl.getD_lt hk) (hl.getD_lt hk1) with h | ⟨d, hd, h⟩
  · grind
  grind

/-- A point of a piece segment in the closure of a set of interior points of `Q` lies on the
boundary of `Q`. -/
theorem IsPiece.mem_boundary_of_closure {S : Set Point}
    (hS : S ⊆ (subPoly P l).filled \ (subPoly P l).boundary) {x y : ℕ} (hx : x < P.n)
    (hy : y < P.n) (he : IsPieceEdge P x y) {q : Point}
    (hq : q ∈ Chazelle.segment (P.vtx x) (P.vtx y)) (hcl : q ∈ closure S) :
    q ∈ (subPoly P l).boundary := by
  have hf : q ∈ (subPoly P l).filled :=
    (isClosed_filled _).closure_subset (closure_mono (fun z hz => (hS hz).1) hcl)
  by_contra hnb
  exact hl.not_mem_attached hx hy he hq ⟨hf, hnb⟩


end

/-- A point of the closure of a set of interior points of `Q` which is on no boundary point of
`Q` is an interior point. -/
theorem IsPiece.mem_int_of_closure {l : List ℕ} {S : Set Point}
    (hS : S ⊆ (subPoly P l).filled \ (subPoly P l).boundary) {q : Point} (hcl : q ∈ closure S)
    (hq : q ∉ (subPoly P l).boundary) : q ∈ (subPoly P l).filled \ (subPoly P l).boundary :=
  ⟨(isClosed_filled _).closure_subset (closure_mono (fun _ hz => (hS hz).1) hcl), hq⟩

/-- **Boundary recognition.**  Let `c = l.getD k 0` be the vertex at position `k` of the piece,
and `[P.vtx c, P.vtx w]` a piece segment whose points near `P.vtx c` are boundary points of
`Q`.  Then `P.vtx w` is the vertex of `Q` at one of the two positions adjacent to `k`. -/
theorem IsPiece.nbr_of_boundary (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) {k : ℕ}
    (hk : k < l.length) {w : ℕ} (hw : w < P.n) (hpe : IsPieceEdge P (l.getD k 0) w)
    (hb : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      lerp (P.vtx (l.getD k 0)) (P.vtx w) s ∈ (subPoly P l).boundary) :
    P.vtx w = (subPoly P l).vtx (prevIdx (subPoly P l) k) ∨
      P.vtx w = (subPoly P l).vtx ((k + 1) % l.length) := by
  set Q := subPoly P l with hQdef
  have hQ : Q.Simple := hl.simple
  have hkQ : k < Q.n := by simp_all
  have hc := hl.getD_lt hk
  set c := l.getD k 0 with hcdef
  obtain ⟨r, hr, hball⟩ := Chazelle.Existence.boundary_near_vtx hQ hkQ
  have htend : Tendsto (lerp (P.vtx c) (P.vtx w)) (𝓝[>] 0) (𝓝 (P.vtx c)) := by
    have := (continuous_lerp (P.vtx c) (P.vtx w)).tendsto 0
    rw [lerp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨s, ⟨hsb, hsB⟩, hs⟩ := ((htend.eventually (isOpen_ball.mem_nhds
    (show P.vtx c ∈ ball (P.vtx c) r from mem_ball_self hr))).and hb |>.and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  have hvk : Q.vtx k = P.vtx c := IsPiece.vtx_eq hk
  have hxc : lerp (P.vtx c) (P.vtx w) s ≠ P.vtx c :=
    lerp_ne_left (hpe.vtx_ne hP hc hw) hs.1
  have hxseg : lerp (P.vtx c) (P.vtx w) s ∈ Chazelle.segment (P.vtx c) (P.vtx w) :=
    lerp_mem_segment _ _ hs.1.le hs.2.le
  have hsb' : lerp (P.vtx c) (P.vtx w) s ∈ ball (Q.vtx k) r := by simp_all
  rcases hball _ hsb' hsB with h | h
  · -- the previous edge of `Q`
    have hpk : prevIdx Q k < l.length := by
      have := prevIdx_lt Q hkQ; simp_all
    have hsucc : (prevIdx Q k + 1) % l.length = k := by
      have := prevIdx_succ Q hkQ; simp_all
    have hedge := hl.edge_at hpk
    rw [hsucc] at hedge
    rw [IsPiece.vtx_eq hpk, hvk] at h
    rw [IsPiece.vtx_eq hpk]
    left
    rw [Geometry.segment_comm] at h
    have := hpe.eq_of_mem_of_mem hP hc hw (hl.getD_lt hpk) hedge.symm hxseg h hxc
    rw [this]
  · have hk1 : (k + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
    have hedge := hl.edge_at hk
    have hQn : Q.n = l.length := by simp_all
    rw [hQn, IsPiece.vtx_eq hk1, hvk] at h
    rw [IsPiece.vtx_eq hk1]
    right
    have := hpe.eq_of_mem_of_mem hP hc hw (hl.getD_lt hk1) hedge hxseg h hxc
    rw [this]

/-! ### Cells of a trapezoid -/

namespace TrapData

section
variable (D : TrapData P)
include D
/-- **The left cell** of a trapezoid region: the part of the region strictly to the left of the
inserted diagonal from the bottom vertex to the top vertex (the whole region if the two vertices
are adjacent and no diagonal is inserted). -/
def cellL : Set Point :=
  {p | p ∈ D.region ∧ (D.NonAdj → 0 < det (P.vtx D.bot) (P.vtx D.top) p)}

/-- **The right cell** of a trapezoid region: the part strictly to the right of the inserted
diagonal (the whole region if no diagonal is inserted). -/
def cellR : Set Point :=
  {p | p ∈ D.region ∧ (D.NonAdj → det (P.vtx D.bot) (P.vtx D.top) p < 0)}


end

section
variable (D : TrapData P)
/-- The left cell is convex. -/
theorem convex_cellL : Convex ℝ D.cellL := by
  by_cases h : D.NonAdj
  · have e : D.cellL = D.region ∩ {p | 0 < (1 : ℝ) * det (P.vtx D.bot) (P.vtx D.top) p} := by
      grind [cellL, mem_ofPred_eq, mem_inter_iff, one_mul]
    rw [e]
    exact (convex_trapSet P D.i D.j D.y₁ D.y₂).inter (convex_det_pos _ _ 1)
  · have e : D.cellL = D.region := by
      simp_all [cellL, mem_ofPred_eq]
    rw [e]
    exact convex_trapSet P D.i D.j D.y₁ D.y₂

/-- The right cell is convex. -/
theorem convex_cellR : Convex ℝ D.cellR := by
  by_cases h : D.NonAdj
  · have e : D.cellR = D.region ∩ {p | 0 < (-1 : ℝ) * det (P.vtx D.bot) (P.vtx D.top) p} := by
      grind [cellR, mem_ofPred_eq, mem_inter_iff, neg_one_mul, neg_pos]
    rw [e]
    exact (convex_trapSet P D.i D.j D.y₁ D.y₂).inter (convex_det_pos _ _ (-1))
  · have e : D.cellR = D.region := by
      simp_all [cellR, mem_ofPred_eq]
    rw [e]
    exact convex_trapSet P D.i D.j D.y₁ D.y₂


end

section
variable (hP : P.Simple) (D : TrapData P)
include hP
/-- The determinant against the diagonal, in coordinates. -/
theorem det_bot_top (p : Point) :
    det (P.vtx D.bot) (P.vtx D.top) p =
      ((P.vtx D.top).1 - (P.vtx D.bot).1) * (p.2 - D.y₁) - (p.1 - (P.vtx D.bot).1) * (D.y₂ - D.y₁) := by
  unfold det
  rw [D.top_snd hP, D.bot_snd hP]

/-- **The only inserted diagonal through a point of a region is the region's own diagonal.** -/
theorem diag_of_mem_region {p : Point} (hp : p ∈ D.region)
    {d : ℕ × ℕ} (hd : d ∈ allDiagonals P) (hpd : p ∈ diagSeg P d) :
    D.NonAdj ∧ det (P.vtx D.bot) (P.vtx D.top) p = 0 := by
  rcases hd with hd | hd
  · obtain ⟨D', hD', rfl⟩ := hd
    rcases D'.segment_cases hP hD' hpd with e | e | e
    · exact absurd (by simp_all) (D.not_mem_region_of_vtx hP (D'.top_lt hP))
    · exact absurd (by simp_all) (D.not_mem_region_of_vtx hP (D'.bot_lt hP))
    · have heq : D.region = D'.region :=
        (regions_eq_or_disjoint (D.region_mem_regions hP) (D'.region_mem_regions hP)).resolve_right
          (fun hdis => Set.disjoint_left.1 hdis hp e)
      have hdiag := diag_eq_of_region_eq hP D D' heq
      have ht : D.top = D'.top := congrArg Prod.fst hdiag
      have hb : D.bot = D'.bot := congrArg Prod.snd hdiag
      refine ⟨?_, ?_⟩
      · core_grind
      · have h0 : det (P.vtx D'.top) (P.vtx D'.bot) p = 0 :=
          Geometry.det_eq_zero_of_mem_segment hpd
        grind [Geometry.det_swap12, neg_zero]
  · exfalso
    have hpc : p ∈ chordUnion P := ⟨diagSeg P d, vtxChords_diagSeg_mem_chords hd, hpd⟩
    exact (D.region_subset_freeRegion hP hp).2 hpc


end

section
variable (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P)
include hP hl
/-- A point of the left cell is not a boundary point of a piece. -/
theorem cellL_not_mem_boundaryQ
    {p : Point} (hp : p ∈ D.cellL) : p ∉ (subPoly P l).boundary := by
  intro hb
  rcases hl.mem_boundary_cases hb with h | ⟨d, hd, hpd⟩
  · exact (D.region_subset_interior hP hp.1).2 h
  · obtain ⟨hna, hdet⟩ := D.diag_of_mem_region hP hp.1 hd hpd
    have := hp.2 hna
    simp_all

/-- A point of the right cell is not a boundary point of a piece. -/
theorem cellR_not_mem_boundaryQ
    {p : Point} (hp : p ∈ D.cellR) : p ∉ (subPoly P l).boundary := by
  intro hb
  rcases hl.mem_boundary_cases hb with h | ⟨d, hd, hpd⟩
  · exact (D.region_subset_interior hP hp.1).2 h
  · obtain ⟨hna, hdet⟩ := D.diag_of_mem_region hP hp.1 hd hpd
    have := hp.2 hna
    simp_all

/-- **A left cell containing an interior point of a piece lies in the interior of the piece.** -/
theorem cellL_subset_intQ
    {p₀ : Point} (hp₀ : p₀ ∈ D.cellL)
    (hi : p₀ ∈ (subPoly P l).filled \ (subPoly P l).boundary) :
    D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary :=
  subset_interior_of_isPreconnected hl.simple D.convex_cellL.isPreconnected
    (fun _ hx => D.cellL_not_mem_boundaryQ hP hl hx) hp₀ hi

/-- **A right cell containing an interior point of a piece lies in the interior of the
piece.** -/
theorem cellR_subset_intQ
    {p₀ : Point} (hp₀ : p₀ ∈ D.cellR)
    (hi : p₀ ∈ (subPoly P l).filled \ (subPoly P l).boundary) :
    D.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary :=
  subset_interior_of_isPreconnected hl.simple D.convex_cellR.isPreconnected
    (fun _ hx => D.cellR_not_mem_boundaryQ hP hl hx) hp₀ hi


end

end TrapData

/-! ### Closures of regions and cells -/

/-- A convex combination of a point of the closed trapezoid and a point of the open trapezoid,
with positive weight on the latter, lies in the open trapezoid. -/
theorem lerp_mem_trapSet {i j : ℕ} {y₁ y₂ : ℝ} {z w : Point}
    (hz : z ∈ closedTrap P i j y₁ y₂) (hw : w ∈ trapSet P i j y₁ y₂) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) : lerp z w s ∈ trapSet P i j y₁ y₂ := by
  obtain ⟨z1, z2, z3, z4⟩ := hz
  obtain ⟨w1, w2, w3, w4⟩ := hw
  have e2 : (lerp z w s).2 = (1 - s) * z.2 + s * w.2 := by core_grind
  have e1 : (lerp z w s).1 = (1 - s) * z.1 + s * w.1 := by core_grind
  have hs' : 0 ≤ 1 - s := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · show y₁ < (lerp z w s).2
    rw [e2]
    nlinarith [mul_nonneg hs' (sub_nonneg.2 z1), mul_pos hs0 (sub_pos.2 w1)]
  · show (lerp z w s).2 < y₂
    rw [e2]
    nlinarith [mul_nonneg hs' (sub_nonneg.2 z2), mul_pos hs0 (sub_pos.2 w2)]
  · show edgeX P i (lerp z w s).2 < (lerp z w s).1
    rw [e2, edgeX_combo P i (by ring : (1 - s) + s = 1), e1]
    nlinarith [mul_nonneg hs' (sub_nonneg.2 z3), mul_pos hs0 (sub_pos.2 w3)]
  · show (lerp z w s).1 < edgeX P j (lerp z w s).2
    rw [e2, edgeX_combo P j (by ring : (1 - s) + s = 1), e1]
    nlinarith [mul_nonneg hs' (sub_nonneg.2 z4), mul_pos hs0 (sub_pos.2 w4)]

namespace TrapData

/-- **The closed trapezoid lies in the closure of the region.** -/
theorem closedTrap_subset_closure (hP : P.Simple) (D : TrapData P) :
    closedTrap P D.i D.j D.y₁ D.y₂ ⊆ closure D.region := by
  intro z hz
  have hw : D.q ∈ D.region := D.isTrap.q_mem hP D.free.1
  have htend : Tendsto (lerp z D.q) (𝓝[>] 0) (𝓝 z) := by
    have := (continuous_lerp z D.q).tendsto 0
    rw [lerp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  exact lerp_mem_trapSet hz hw hs.1 hs.2.le

section
variable (hP : P.Simple) (D : TrapData P) {z : Point} (hz : z ∈ closedTrap P D.i D.j D.y₁ D.y₂)
include hP hz
/-- A point of the closed trapezoid strictly to the left of the diagonal is in the closure of
the left cell. -/
theorem mem_closure_cellL
    (hdet : D.NonAdj → 0 < det (P.vtx D.bot) (P.vtx D.top) z) : z ∈ closure D.cellL := by
  by_cases h : D.NonAdj
  · have hU : IsOpen {p : Point | 0 < det (P.vtx D.bot) (P.vtx D.top) p} := by
      have := isOpen_det_pos (P.vtx D.bot) (P.vtx D.top) 1
      simp_all
    have := hU.inter_closure ⟨hdet h, D.closedTrap_subset_closure hP hz⟩
    have hsub : {p : Point | 0 < det (P.vtx D.bot) (P.vtx D.top) p} ∩ D.region ⊆ D.cellL :=
      fun p hp => ⟨hp.2, fun _ => hp.1⟩
    exact closure_mono hsub this
  · have hsub : D.region ⊆ D.cellL := fun p hp => ⟨hp, fun h' => absurd h' h⟩
    exact closure_mono hsub (D.closedTrap_subset_closure hP hz)

/-- A point of the closed trapezoid strictly to the right of the diagonal is in the closure of
the right cell. -/
theorem mem_closure_cellR
    (hdet : D.NonAdj → det (P.vtx D.bot) (P.vtx D.top) z < 0) : z ∈ closure D.cellR := by
  by_cases h : D.NonAdj
  · have hU : IsOpen {p : Point | det (P.vtx D.bot) (P.vtx D.top) p < 0} := by
      have := isOpen_det_pos (P.vtx D.bot) (P.vtx D.top) (-1)
      simp_all
    have := hU.inter_closure ⟨hdet h, D.closedTrap_subset_closure hP hz⟩
    have hsub : {p : Point | det (P.vtx D.bot) (P.vtx D.top) p < 0} ∩ D.region ⊆ D.cellR :=
      fun p hp => ⟨hp.2, fun _ => hp.1⟩
    exact closure_mono hsub this
  · have hsub : D.region ⊆ D.cellR := fun p hp => ⟨hp, fun h' => absurd h' h⟩
    exact closure_mono hsub (D.closedTrap_subset_closure hP hz)


end

section
variable (hP : P.Simple) (D : TrapData P) {z : Point} (hz : z ∈ D.region) (hdet : det (P.vtx D.bot) (P.vtx D.top) z = 0)
include hP hz hdet
/-- A point of the region on the line of the diagonal is in the closure of both cells. -/
theorem mem_closure_cells_of_region :
    z ∈ closure D.cellL ∧ z ∈ closure D.cellR := by
  by_cases h : D.NonAdj
  · set b := P.vtx D.bot
    set t := P.vtx D.top
    have hbt : 0 < t.2 - b.2 := by
      have := D.bot_snd_lt_top_snd hP; linarith
    set L := (t.1 - b.1) ^ 2 + (t.2 - b.2) ^ 2 with hL
    have hLpos : 0 < L := by positivity
    let f : ℝ → Point := fun ε => (z.1 - ε * (t.2 - b.2), z.2 + ε * (t.1 - b.1))
    have hf : Continuous f := by fun_prop
    have hf0 : f 0 = z := by simp [f]
    have hdetf : ∀ ε, det b t (f ε) = ε * L := by
      intro ε
      have e : det b t (f ε) = det b t z + ε * L := by
        simp only [f, det, hL]; ring
      simp_all
    have hreg : ∀ᶠ ε in 𝓝 (0 : ℝ), f ε ∈ D.region := by
      have := hf.tendsto 0
      rw [hf0] at this
      exact this.eventually ((isOpen_trapSet P D.i D.j D.y₁ D.y₂).mem_nhds hz)
    constructor
    · have htend : Tendsto f (𝓝[>] 0) (𝓝 z) := by
        have := hf.tendsto 0
        rw [hf0] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto htend ?_
      filter_upwards [nhdsWithin_le_nhds hreg, self_mem_nhdsWithin] with ε hε hε0
      refine ⟨hε, fun _ => ?_⟩
      simp_all +zetaDelta 
    · have htend : Tendsto f (𝓝[<] 0) (𝓝 z) := by
        have := hf.tendsto 0
        rw [hf0] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto htend ?_
      filter_upwards [nhdsWithin_le_nhds hreg, self_mem_nhdsWithin] with ε hε hε0
      refine ⟨hε, fun _ => ?_⟩
      rw [hdetf]
      exact mul_neg_of_neg_of_pos hε0 hLpos
  · exact ⟨subset_closure ⟨hz, fun h' => absurd h' h⟩, subset_closure ⟨hz, fun h' => absurd h' h⟩⟩

/-- A point of the region on the line of the diagonal lies on the diagonal. -/
theorem mem_diagSeg_of_det : z ∈ diagSeg P D.diag := by
  have hb2 := D.bot_snd hP
  have ht2 := D.top_snd hP
  
  have hz1 : D.y₁ < z.2 := hz.1
  have hz2 : z.2 < D.y₂ := hz.2.1
  rw [D.det_bot_top hP] at hdet
  set s := (D.y₂ - z.2) / (D.y₂ - D.y₁) with hs
  have hne : D.y₂ - D.y₁ ≠ 0 := by linarith
  refine ⟨s, div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith),
    ?_⟩
  grind [Geometry.point_ext_iff, diag]


end

/-- On the open left and right side edges, the determinant against the diagonal has the sign of
the corresponding cell. -/
theorem det_side (hP : P.Simple) (D : TrapData P) (hna : D.NonAdj) {h : ℝ} (h1 : D.y₁ < h)
    (h2 : h < D.y₂) :
    0 < det (P.vtx D.bot) (P.vtx D.top) (edgeX P D.i h, h) ∧
      det (P.vtx D.bot) (P.vtx D.top) (edgeX P D.j h, h) < 0 := by
  have hb2 := D.bot_snd hP
  have ht2 := D.top_snd hP
  set s := (D.y₂ - h) / (D.y₂ - D.y₁) with hs
  have hne : 0 < D.y₂ - D.y₁ := by linarith
  have hs0 : 0 < s := div_pos (by linarith) hne
  have hs1 : s < 1 := (div_lt_one hne).2 (by linarith)
  set d := lerp (P.vtx D.top) (P.vtx D.bot) s with hd'
  have hd : d ∈ D.region := D.isTrap.diag_lerp_mem_trapSet hP D.free hna.1 hna.2 hs0 hs1
  have hd2 : d.2 = h := by
    grind [lerp_snd]
  have hdet0 : det (P.vtx D.bot) (P.vtx D.top) d = 0 := by
    rw [Geometry.det_swap12]
    rw [Geometry.det_eq_zero_of_mem_segment (lerp_mem_segment _ _ hs0.le hs1.le), neg_zero]
  have key : ∀ X : ℝ, det (P.vtx D.bot) (P.vtx D.top) (X, h) = (d.1 - X) * (D.y₂ - D.y₁) := by
    intro X
    have e1 := D.det_bot_top hP (X, h)
    have e2 := D.det_bot_top hP d
    grind
  have hdi : edgeX P D.i h < d.1 := by
    have := hd.2.2.1; grind
  have hdj : d.1 < edgeX P D.j h := by
    have := hd.2.2.2; grind
  refine ⟨?_, ?_⟩
  · simp_all
  · rw [key]; exact mul_neg_of_neg_of_pos (by linarith) hne

end TrapData

/-! ### Gaps on the top side -/

/-- If a point strictly between two abscissae `a < x < b` lies on a horizontal segment whose
endpoints are not strictly between `a` and `b` and differ from the point, then the segment
contains the points of abscissae `a` and `b`. -/
theorem horiz_seg_ends {u w : Point} {y a b x : ℝ} (hu : u.2 = y) (hw : w.2 = y)
    (hx : ((x, y) : Point) ∈ Chazelle.segment u w) (hxu : x ≠ u.1) (hxw : x ≠ w.1)
    (hua : ¬ (a < u.1 ∧ u.1 < b)) (hwa : ¬ (a < w.1 ∧ w.1 < b)) (hx1 : a < x) (hx2 : x < b) :
    ((a, y) : Point) ∈ Chazelle.segment u w ∧ ((b, y) : Point) ∈ Chazelle.segment u w := by
  have huw : u.2 = w.2 := hu.trans hw.symm
  rw [segment_horizontal_eq_hseg huw] at hx ⊢
  obtain ⟨-, hx3, hx4⟩ := hx
  simp only at hx3 hx4
  have hmin : min u.1 w.1 ≤ a := by
    core_grind
  have hmax : b ≤ max u.1 w.1 := by
    core_grind
  exact ⟨⟨hu.symm ▸ rfl, hmin, by linarith⟩, ⟨hu.symm ▸ rfl, by linarith, hmax⟩⟩

namespace TrapData

section
variable (hP : P.Simple) (D : TrapData P)
include hP
/-- **Gap lemma (top side).**  Let `(a, b) × {y₂}` be a portion of the closed top side of a
trapezoid carrying no vertex of `P`, one of whose ends is an interior point of a
non-horizontal edge `e`.  Then its points are not on the boundary of `P`, are chord points,
and lie on no inserted diagonal. -/
theorem gap_top {a b : ℝ}
    (ha : edgeX P D.i D.y₂ ≤ a) (hb : b ≤ edgeX P D.j D.y₂)
    (hnov : ∀ k, k < P.n → (P.vtx k).2 = D.y₂ → a < (P.vtx k).1 → (P.vtx k).1 < b → False)
    {e : ℕ} (he : e < P.n) (hnh : NonHoriz P e)
    (hend : OpenEdgePt P e (a, D.y₂) ∨ OpenEdgePt P e (b, D.y₂))
    {x : ℝ} (hx1 : a < x) (hx2 : x < b) :
    ((x, D.y₂) : Point) ∉ P.boundary ∧ ((x, D.y₂) : Point) ∈ chordUnion P ∧
      ∀ d ∈ allDiagonals P, ((x, D.y₂) : Point) ∉ diagSeg P d := by
  have hnv : ∀ k, k < P.n → ((x, D.y₂) : Point) ≠ P.vtx k := by
    grind
  have hi : edgeX P D.i D.y₂ < x := lt_of_le_of_lt ha hx1
  have hj : x < edgeX P D.j D.y₂ := lt_of_lt_of_le hx2 hb
  -- the end point on `e` lies on no horizontal segment through the gap which is an edge
  have hXb : ((x, D.y₂) : Point) ∉ P.boundary := by
    intro hXb
    obtain ⟨g, hg, t, ht, hXe⟩ := exists_openEdge_of_mem_boundary P hXb hnv
    have hoe : OpenEdgePt P g (x, D.y₂) := ⟨t, ht, hXe⟩
    by_cases hgh : NonHoriz P g
    · exact side_edge_false (Or.inr rfl) (D.region_subset_interior hP) rfl
        (D.isTrap.near_top hi hj) hg hgh hoe
    · unfold NonHoriz at hgh
      push Not at hgh
      have hy : D.y₂ = (P.vtx g).2 := by
        have := congrArg Prod.snd hXe
        simp_all
      have hu2 : (P.vtx g).2 = D.y₂ := hy.symm
      have hw2 : (P.vtx ((g + 1) % P.n)).2 = D.y₂ := hgh ▸ hu2
      have hXs : ((x, D.y₂) : Point) ∈ Chazelle.segment (P.vtx g) (P.vtx ((g + 1) % P.n)) :=
        hoe.mem_edge
      have hxu : x ≠ (P.vtx g).1 := fun h =>
        hnv g hg (point_ext h (hu2.symm))
      have hxw : x ≠ (P.vtx ((g + 1) % P.n)).1 := fun h =>
        hnv _ (succIdx_lt P hg) (point_ext h (hw2.symm))
      have ends := horiz_seg_ends hu2 hw2 hXs hxu hxw
        (fun h => hnov g hg hu2 h.1 h.2) (fun h => hnov _ (succIdx_lt P hg) hw2 h.1 h.2) hx1 hx2
      have hge : g ≠ e := by
        rintro rfl; exact hnh hgh
      rcases hend with hoe' | hoe'
      · exact hoe'.not_mem_other hP he hg hge ends.1
      · exact hoe'.not_mem_other hP he hg hge ends.2
  have hXc : ((x, D.y₂) : Point) ∈ chordUnion P :=
    (D.isTrap.top_side hP D.free hi hj).resolve_left hXb
  refine ⟨hXb, hXc, ?_⟩
  intro d hd hXd
  rcases hd with hd | hd
  · obtain ⟨D', hD', rfl⟩ := hd
    rcases D'.segment_cases hP hD' hXd with h | h | h
    · exact hnv _ (D'.top_lt hP) h
    · exact hnv _ (D'.bot_lt hP) h
    · exact (D'.region_subset_freeRegion hP h).2 hXc
  · have hsnd := vtxChords_snd_eq hd
    have hd1 : d.1 < P.n := hd.1
    have hd2 : d.2 < P.n := hd.2.1
    have hy : (P.vtx d.1).2 = D.y₂ := by
      obtain ⟨t, -, -, h⟩ := hXd
      grind
    have hy' : (P.vtx d.2).2 = D.y₂ := hsnd ▸ hy
    have hxu : x ≠ (P.vtx d.1).1 := fun h => hnv _ hd1 (point_ext h hy.symm)
    have hxw : x ≠ (P.vtx d.2).1 := fun h => hnv _ hd2 (point_ext h hy'.symm)
    have ends := horiz_seg_ends hy hy' hXd hxu hxw (fun h => hnov _ hd1 hy h.1 h.2)
      (fun h => hnov _ hd2 hy' h.1 h.2) hx1 hx2
    rcases hend with hoe' | hoe'
    · exact allDiagonals_not_mem_boundary hP (Or.inr hd) ends.1 (hoe'.ne_vtx hP he hd1)
        (hoe'.ne_vtx hP he hd2) (hoe'.mem_boundary he)
    · exact allDiagonals_not_mem_boundary hP (Or.inr hd) ends.2 (hoe'.ne_vtx hP he hd1)
        (hoe'.ne_vtx hP he hd2) (hoe'.mem_boundary he)

/-- If an interior point `(a, y₁)` of a non-horizontal edge `e` lies on the closed bottom side of
a trapezoid, strictly left of its right end, it is the left corner and `e` is the left side
edge. -/
theorem i_eq_of_openEdgePt {a : ℝ}
    (hle : edgeX P D.i D.y₁ ≤ a) (hlt : a < edgeX P D.j D.y₁) {e : ℕ} (he : e < P.n)
    (hnh : NonHoriz P e) (hoe : OpenEdgePt P e (a, D.y₁)) : D.i = e := by
  rcases hle.lt_or_eq with h | h
  · exact absurd (side_edge_false (Or.inl rfl) (D.region_subset_interior hP) rfl
      (D.isTrap.near_bot h hlt) he hnh hoe) not_false
  · have hmem : ((a, D.y₁) : Point) ∈ P.edge D.i :=
      D.isTrap.mem_edgeL le_rfl (D.isTrap.bot_lt.trans D.isTrap.lt_top).le h.symm
    by_contra hne
    exact hoe.not_mem_other hP he D.isTrap.hi hne hmem

/-- If an interior point `(b, y₁)` of a non-horizontal edge `e` lies on the closed bottom side of
a trapezoid, strictly right of its left end, it is the right corner and `e` is the right side
edge. -/
theorem j_eq_of_openEdgePt {b : ℝ}
    (hlt : edgeX P D.i D.y₁ < b) (hle : b ≤ edgeX P D.j D.y₁) {e : ℕ} (he : e < P.n)
    (hnh : NonHoriz P e) (hoe : OpenEdgePt P e (b, D.y₁)) : D.j = e := by
  rcases hle.lt_or_eq with h | h
  · exact absurd (side_edge_false (Or.inl rfl) (D.region_subset_interior hP) rfl
      (D.isTrap.near_bot hlt h) he hnh hoe) not_false
  · have hmem : ((b, D.y₁) : Point) ∈ P.edge D.j :=
      D.isTrap.mem_edgeR le_rfl (D.isTrap.bot_lt.trans D.isTrap.lt_top).le h
    by_contra hne
    exact hoe.not_mem_other hP he D.isTrap.hj hne hmem


end

section
variable (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P) {x : ℝ} (hx1 : edgeX P D.i D.y₁ < x) (hx2 : x < edgeX P D.j D.y₁)
include hP hl hx1 hx2
/-- **Left cell above a bottom point.**  If the point `(x, y₁)` of the open bottom side, strictly
left of the bottom vertex, is an interior point of a piece, the left cell lies in the interior
of the piece. -/
theorem cellL_subset_of_bot
    (hxb : x < (P.vtx D.bot).1)
    (hxi : ((x, D.y₁) : Point) ∈ (subPoly P l).filled \ (subPoly P l).boundary) :
    D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary := by
  have hopen := isOpen_filled_sdiff_boundary hl.simple
  have h12 : D.y₁ < D.y₂ := D.isTrap.bot_lt.trans D.isTrap.lt_top
  have hdet0 : 0 < det (P.vtx D.bot) (P.vtx D.top) (x, D.y₁) := by
    rw [D.det_bot_top hP]; nlinarith
  have hU : IsOpen {p : Point | 0 < det (P.vtx D.bot) (P.vtx D.top) p} := by
    have := isOpen_det_pos (P.vtx D.bot) (P.vtx D.top) 1
    simp_all
  have hev := ((D.isTrap.near_bot hx1 hx2).and (hopen.mem_nhds hxi)).and (hU.mem_nhds hdet0)
  have htend : Tendsto (fun δ : ℝ => ((x, D.y₁ + δ) : Point)) (𝓝[>] 0) (𝓝 (x, D.y₁)) := by
    have hc : Continuous fun δ : ℝ => ((x, D.y₁ + δ) : Point) := by fun_prop
    have := hc.tendsto 0
    simp only [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨δ, ⟨⟨h1, h2⟩, h3⟩, hδ⟩ := ((htend.eventually hev).and self_mem_nhdsWithin).exists
  have hδ' : (0 : ℝ) < δ := hδ
  have hreg : ((x, D.y₁ + δ) : Point) ∈ D.region := h1 (by simp_all)
  exact D.cellL_subset_intQ hP hl ⟨hreg, fun _ => h3⟩ h2

/-- **Right cell above a bottom point.**  If the point `(x, y₁)` of the open bottom side, strictly
right of the bottom vertex, is an interior point of a piece, the right cell lies in the
interior of the piece. -/
theorem cellR_subset_of_bot
    (hxb : (P.vtx D.bot).1 < x)
    (hxi : ((x, D.y₁) : Point) ∈ (subPoly P l).filled \ (subPoly P l).boundary) :
    D.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary := by
  have hopen := isOpen_filled_sdiff_boundary hl.simple
  have h12 : D.y₁ < D.y₂ := D.isTrap.bot_lt.trans D.isTrap.lt_top
  have hdet0 : det (P.vtx D.bot) (P.vtx D.top) (x, D.y₁) < 0 := by
    rw [D.det_bot_top hP]; simp_all
  have hU : IsOpen {p : Point | det (P.vtx D.bot) (P.vtx D.top) p < 0} := by
    have := isOpen_det_pos (P.vtx D.bot) (P.vtx D.top) (-1)
    simp_all
  have hev := ((D.isTrap.near_bot hx1 hx2).and (hopen.mem_nhds hxi)).and (hU.mem_nhds hdet0)
  have htend : Tendsto (fun δ : ℝ => ((x, D.y₁ + δ) : Point)) (𝓝[>] 0) (𝓝 (x, D.y₁)) := by
    have hc : Continuous fun δ : ℝ => ((x, D.y₁ + δ) : Point) := by fun_prop
    have := hc.tendsto 0
    simp only [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨δ, ⟨⟨h1, h2⟩, h3⟩, hδ⟩ := ((htend.eventually hev).and self_mem_nhdsWithin).exists
  have hδ' : (0 : ℝ) < δ := hδ
  have hreg : ((x, D.y₁ + δ) : Point) ∈ D.region := h1 (by simp_all)
  exact D.cellR_subset_intQ hP hl ⟨hreg, fun _ => h3⟩ h2


end

end TrapData

/-- **The trapezoid above a horizontal segment of interior chord points.**  If every point of
the open segment `(a, b) × {y₀}` is an interior chord point of `P`, some trapezoid has bottom
height `y₀` and a closed bottom side containing the segment. -/
theorem exists_trapData_above (hP : P.Simple) {y₀ a b : ℝ} (hab : a < b)
    (hint : ∀ x, a < x → x < b → ((x, y₀) : Point) ∈ P.filled \ P.boundary)
    (hch : ∀ x, a < x → x < b → ((x, y₀) : Point) ∈ chordUnion P) :
    ∃ D : TrapData P, D.y₁ = y₀ ∧ edgeX P D.i y₀ ≤ a ∧ b ≤ edgeX P D.j y₀ := by
  set x₀ := (a + b) / 2 with hx₀
  have hxa : a < x₀ := by linarith
  have hxb : x₀ < b := by linarith
  set z : Point := (x₀, y₀) with hz
  have hzi : z ∈ P.filled \ P.boundary := hint x₀ hxa hxb
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (isOpen_filled_sdiff_boundary hP) z hzi
  obtain ⟨g, hg, hgle⟩ := exists_pos_le_of_pos (fun k => (P.vtx k).2 - y₀) P.n
  set U := ball z ρ ∩ {p : Point | p.2 < y₀ + g} with hU
  have hUo : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_snd continuous_const)
  have hzU : z ∈ U := ⟨mem_ball_self hρ, by grind⟩
  obtain ⟨q, ⟨hqb, hqg⟩, hqf, hq1, hq2⟩ := exists_free_of_isOpen hP hUo hzU hzi
  simp only [hz] at hq1 hq2
  obtain ⟨i, j, y₁, y₂, hT, hreg⟩ := exists_isTrap_region_eq hP hqf
  let D : TrapData P := ⟨q, i, j, y₁, y₂, hqf, hT⟩
  
  -- the vertical segment from `z` up to `q` lies in the region
  have hV : ∀ y, y₀ < y → y ≤ q.2 → ((x₀, y) : Point) ∈ trapSet P i j y₁ y₂ := by
    set V := (fun y : ℝ => ((x₀, y) : Point)) '' Ioc y₀ q.2 with hVdef
    have hVc : IsPreconnected V :=
      isPreconnected_Ioc.image _ (by fun_prop : Continuous fun y : ℝ => ((x₀, y) : Point)).continuousOn
    have hqV : q ∈ V := ⟨q.2, ⟨hq2, le_rfl⟩, by rw [← hq1]⟩
    have hVf : V ⊆ freeRegion P := by
      rintro _ ⟨y, hy, rfl⟩
      have hyb : ((x₀, y) : Point) ∈ ball z ρ := by
        rw [mem_ball_iff_abs]
        have hqb' := hqb
        rw [mem_ball_iff_abs] at hqb'
        simp only [hz, sub_self, abs_zero] at hqb' ⊢
        grind
      refine ⟨hball hyb, fun hc => ?_⟩
      obtain ⟨k, hk, hks⟩ := chordUnion_snd hc
      core_grind
    have hsub : V ⊆ connectedComponentIn (freeRegion P) q :=
      hVc.subset_connectedComponentIn hqV hVf
    grind
  have hy1le : y₁ ≤ y₀ := by
    by_contra h
    push Not at h
    have := hV (min q.2 y₁) (lt_min hq2 h) (min_le_left _ _)
    exact absurd this.1 (not_lt.2 (min_le_right _ _))
  -- the point `z` is in the closure of the region
  have hzc : z ∈ closure (trapSet P i j y₁ y₂) := by
    have htend : Tendsto (fun y : ℝ => ((x₀, y) : Point)) (𝓝[>] y₀) (𝓝 z) := by
      have hc : Continuous fun y : ℝ => ((x₀, y) : Point) := by fun_prop
      exact (hc.tendsto y₀).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsGT hq2] with y hy
    grind
  obtain ⟨hc1, hc2, hc3, hc4⟩ := closure_trapSet_subset P i j y₁ y₂ hzc
  simp only [hz] at hc1 hc2 hc3 hc4
  have hy1ge : y₀ ≤ y₁ := by
    by_contra h
    push Not at h
    have hL : edgeX P i y₀ < x₀ := by
      refine lt_of_le_of_ne hc3 (fun e => hzi.2 ⟨i, hT.hi, ?_⟩)
      exact hT.mem_edgeL (p := z) h.le hc2 e.symm
    have hR : x₀ < edgeX P j y₀ := by
      refine lt_of_le_of_ne hc4 (fun e => hzi.2 ⟨j, hT.hj, ?_⟩)
      exact hT.mem_edgeR (p := z) h.le hc2 e
    have hmem : z ∈ trapSet P i j y₁ y₂ := ⟨h, lt_of_lt_of_le hq2 hT.lt_top.le |>.trans_le le_rfl
      |> fun h' => by omega, hL, hR⟩
    exact (hT.trapSet_subset_freeRegion hP hqf hmem).2 (hch x₀ hxa hxb)
  have hy : y₁ = y₀ := le_antisymm hy1le hy1ge
  refine ⟨D, hy, ?_, ?_⟩
  · show edgeX P i y₀ ≤ a
    by_contra h
    push Not at h
    have hX : ((edgeX P i y₀, y₀) : Point) ∈ P.boundary :=
      ⟨i, hT.hi, hT.mem_edgeL (by rw [hy]) (by omega) rfl⟩
    grind
  · show b ≤ edgeX P j y₀
    by_contra h
    push Not at h
    have hX : ((edgeX P j y₀, y₀) : Point) ∈ P.boundary :=
      ⟨j, hT.hj, hT.mem_edgeR (by rw [hy]) (by omega) rfl⟩
    grind

end

end Chazelle.Mountain
