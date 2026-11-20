module

public import Chazelle.Mountain.PieceCells

/-!
# The climbing steps inside a piece

Let `l` be a piece of the subdivision of the simple polygon `P` by `allDiagonals P`, and
`Q = subPoly P l`.  This file proves the elementary *climbing steps* used to walk up the
boundary of `Q` from its lowest vertex (`Chazelle.Mountain.PiecesMain`).

The walk keeps a trapezoid `D` of the visibility map of `P` one of whose cells lies in the
interior of `Q`, and whose side edge on that side is a fixed edge `e` of `P` (the future base of
the mountain):

* `StateL P l e c`: `D.i = e`, the left cell of `D` is interior to `Q`, and `c` is a vertex of the
  closed bottom side of `D` or the top vertex of `D`;
* `StateR P l e c`: `D.j = e`, the right cell of `D` is interior to `Q`, and `c` is the bottom
  vertex of `D` or a vertex of the closed top side of `D`.

**Steps** (`StateL.step`, `StateR.step`): if the vertex `c` at position `k` of `Q` is in one of
these states and does not lie on `e`, then some neighbour `w` of `c` in `Q` is strictly
`ylexLT`-above `c` and is again in the same state.  The steps are:

* from a vertex of the bottom side to the next vertex to the right on the bottom side
  (`TrapData.bot_right_nbr`), or from the bottom vertex to the top vertex through the inserted
  diagonal or the side edge (`TrapData.bot_top_nbr`);
* from a vertex of the top side to the next vertex to the right (`TrapData.top_right_nbr`);
* across a chord on the top side to the next trapezoid above (`TrapData.gap_left`,
  `TrapData.gap_right`).

In each case the segment followed is a piece segment in the closure of the interior cell, hence
a boundary segment of `Q`, hence an edge of `Q` at `c` (`IsPiece.nbr_of_boundary`).
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

/-- A point of an edge different from both endpoints lies on the open edge. -/
theorem openEdgePt_of_mem_edge_ne {e : ℕ} {p : Point} (h : p ∈ P.edge e) (h1 : p ≠ P.vtx e)
    (h2 : p ≠ P.vtx ((e + 1) % P.n)) : OpenEdgePt P e p := by
  obtain ⟨t, ht0, ht1, rfl⟩ := h
  refine ⟨t, ⟨lt_of_le_of_ne ht0 ?_, lt_of_le_of_ne ht1 ?_⟩, rfl⟩
  · rintro rfl
    apply h1
    rw [Geometry.point_ext_iff]; simp
  · rintro rfl
    apply h2
    rw [Geometry.point_ext_iff]; simp

namespace TrapData

/-- The closed bottom side lies in the closed trapezoid. -/
theorem mem_closedTrap_bot (D : TrapData P) {x : ℝ}
    (h1 : edgeX P D.i D.y₁ ≤ x) (h2 : x ≤ edgeX P D.j D.y₁) :
    ((x, D.y₁) : Point) ∈ closedTrap P D.i D.j D.y₁ D.y₂ :=
  ⟨le_rfl, (D.isTrap.bot_lt.trans D.isTrap.lt_top).le, h1, h2⟩

/-- The closed top side lies in the closed trapezoid. -/
theorem mem_closedTrap_top (D : TrapData P) {x : ℝ}
    (h1 : edgeX P D.i D.y₂ ≤ x) (h2 : x ≤ edgeX P D.j D.y₂) :
    ((x, D.y₂) : Point) ∈ closedTrap P D.i D.j D.y₁ D.y₂ :=
  ⟨(D.isTrap.bot_lt.trans D.isTrap.lt_top).le, le_rfl, h1, h2⟩

/-- The segment from the bottom vertex to the top vertex is a piece segment. -/
theorem isPieceEdge_bot_top (D : TrapData P) : IsPieceEdge P D.bot D.top := by
  by_cases h : D.NonAdj
  · exact Or.inr (Or.inr (Or.inr (Or.inl (D.diag_mem_trapDiagonals h))))
  · unfold NonAdj at h
    rw [not_and_or, not_not, not_not] at h
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h

/-- **From the bottom vertex to the top vertex.**  If the bottom vertex of `D` is the vertex at
position `k` of the piece and one cell of `D` is interior to the piece, then the top vertex is
a neighbour of position `k` in the piece. -/
theorem bot_top_nbr (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P) {k : ℕ}
    (hk : k < l.length) (hc : l.getD k 0 = D.bot)
    (hS : D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary ∨
      D.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary) :
    P.vtx D.top = (subPoly P l).vtx (prevIdx (subPoly P l) k) ∨
      P.vtx D.top = (subPoly P l).vtx ((k + 1) % l.length) := by
  have hpe := D.isPieceEdge_bot_top
  have hpe' : IsPieceEdge P (l.getD k 0) D.top := by rw [hc]; exact hpe
  apply hl.nbr_of_boundary hP hk (D.top_lt hP) hpe'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  rw [hc]
  have hlerp : lerp (P.vtx D.bot) (P.vtx D.top) s = lerp (P.vtx D.top) (P.vtx D.bot) (1 - s) := by
    rw [Geometry.point_ext_iff]; simp only [lerp_fst, lerp_snd]; constructor <;> ring
  have hseg : lerp (P.vtx D.bot) (P.vtx D.top) s ∈
      Chazelle.segment (P.vtx D.bot) (P.vtx D.top) := lerp_mem_segment _ _ hs.1.le hs.2.le
  have hcl : lerp (P.vtx D.bot) (P.vtx D.top) s ∈ closure D.cellL ∧
      lerp (P.vtx D.bot) (P.vtx D.top) s ∈ closure D.cellR := by
    rw [hlerp]
    by_cases h : D.NonAdj
    · have hreg : lerp (P.vtx D.top) (P.vtx D.bot) (1 - s) ∈ D.region :=
        D.isTrap.diag_lerp_mem_trapSet hP D.free h.1 h.2 (by linarith [hs.2]) (by linarith [hs.1])
      have hdet : det (P.vtx D.bot) (P.vtx D.top) (lerp (P.vtx D.top) (P.vtx D.bot) (1 - s)) = 0 := by
        rw [Geometry.det_swap12, Geometry.det_eq_zero_of_mem_segment
          (lerp_mem_segment _ _ (by linarith [hs.2]) (by linarith [hs.1])), neg_zero]
      exact D.mem_closure_cells_of_region hP hreg hdet
    · have hct : lerp (P.vtx D.top) (P.vtx D.bot) (1 - s) ∈ closedTrap P D.i D.j D.y₁ D.y₂ :=
        D.isTrap.diag_lerp_mem_closedTrap hP D.free (by linarith [hs.2]) (by linarith [hs.1])
      exact ⟨D.mem_closure_cellL hP hct (fun h' => absurd h' h),
        D.mem_closure_cellR hP hct (fun h' => absurd h' h)⟩
  rcases hS with hS | hS
  · exact hl.mem_boundary_of_closure hS (D.bot_lt hP) (D.top_lt hP) hpe hseg hcl.1
  · exact hl.mem_boundary_of_closure hS (D.bot_lt hP) (D.top_lt hP) hpe hseg hcl.2

/-- **Along the bottom side.**  If a vertex `c` of the closed bottom side of `D`, other than the
bottom vertex, is the vertex at position `k` of the piece and the left cell is interior to the
piece, then the next vertex `w` to the right on the bottom side is a neighbour of position `k`. -/
theorem bot_right_nbr (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P) {k : ℕ}
    (hk : k < l.length) {c : ℕ} (hc : l.getD k 0 = c) (hcS : c ∈ sideVtxSet P D.i D.j D.y₁)
    (hcb : c ≠ D.bot) (hS : D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary) :
    ∃ w, w ∈ sideVtxSet P D.i D.j D.y₁ ∧ (P.vtx c).1 < (P.vtx w).1 ∧
      (P.vtx w = (subPoly P l).vtx (prevIdx (subPoly P l) k) ∨
        P.vtx w = (subPoly P l).vtx ((k + 1) % l.length)) := by
  obtain ⟨hbmem, hbmax⟩ := D.isTrap.botVtx_spec hP D.free
  change D.bot ∈ sideVtxSet P D.i D.j D.y₁ at hbmem
  change ∀ k ∈ sideVtxSet P D.i D.j D.y₁, (P.vtx k).1 ≤ (P.vtx D.bot).1 at hbmax
  have hkb : (P.vtx c).1 < (P.vtx D.bot).1 := by
    refine lt_of_le_of_ne (hbmax c hcS) (fun h => hcb ?_)
    exact simple_vtx_inj hP hcS.1 hbmem.1 (point_ext h (hcS.2.1.trans hbmem.2.1.symm))
  set S : Set ℕ := {j | j ∈ sideVtxSet P D.i D.j D.y₁ ∧ (P.vtx c).1 < (P.vtx j).1} with hSdef
  have hSfin : S.Finite := (sideVtxSet_finite P D.i D.j D.y₁).subset fun _ h => h.1
  have hSne : S.Nonempty := ⟨D.bot, hbmem, hkb⟩
  obtain ⟨hmS, hmmin⟩ := leftmostVtx_spec P hSfin hSne
  set w := leftmostVtx P S with hwdef
  have hres := gap_adjacent_or_chord hP (Or.inl rfl) (D.region_subset_interior hP)
    hcS.1 hmS.1.1 hcS.2.1 hmS.1.2.1 hmS.2
    (fun x hx1 hx2 => D.isTrap.near_bot (by linarith [hcS.2.2.1]) (by linarith [hmS.1.2.2.2]))
    (fun j hj hjy hj1 hj2 => by
      have hjS : j ∈ S := ⟨⟨hj, hjy, by linarith [hcS.2.2.1], by linarith [hmS.1.2.2.2]⟩, hj1⟩
      linarith [hmmin j hjS])
  have hpe : IsPieceEdge P c w := by
    rcases hres with (h | h) | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
  refine ⟨w, hmS.1, hmS.2, ?_⟩
  have hpe' : IsPieceEdge P (l.getD k 0) w := by rw [hc]; exact hpe
  apply hl.nbr_of_boundary hP hk hmS.1.1 hpe'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  rw [hc]
  have hseg := lerp_mem_segment (P.vtx c) (P.vtx w) hs.1.le hs.2.le
  have hcy := hcS.2.1
  have hwy := hmS.1.2.1
  have hwb := hbmax w hmS.1
  have hp : lerp (P.vtx c) (P.vtx w) s =
      (((P.vtx c).1 + s * ((P.vtx w).1 - (P.vtx c).1), D.y₁) : Point) := by
    rw [Geometry.point_ext_iff]
    refine ⟨rfl, ?_⟩
    show (P.vtx c).2 + s * ((P.vtx w).2 - (P.vtx c).2) = D.y₁
    rw [hcy, hwy]; ring
  have h12 : D.y₁ < D.y₂ := D.isTrap.bot_lt.trans D.isTrap.lt_top
  have hx1 : (P.vtx c).1 ≤ (P.vtx c).1 + s * ((P.vtx w).1 - (P.vtx c).1) := by
    nlinarith [hs.1, hmS.2]
  have hx2 : (P.vtx c).1 + s * ((P.vtx w).1 - (P.vtx c).1) < (P.vtx w).1 := by
    nlinarith [hs.2, hmS.2]
  have hcl : lerp (P.vtx c) (P.vtx w) s ∈ closure D.cellL := by
    rw [hp]
    refine D.mem_closure_cellL hP (D.mem_closedTrap_bot (by linarith [hcS.2.2.1])
      (by linarith [hmS.1.2.2.2])) (fun _ => ?_)
    rw [D.det_bot_top hP]
    simp only [sub_self, mul_zero, zero_sub]
    nlinarith
  exact hl.mem_boundary_of_closure hS hcS.1 hmS.1.1 hpe hseg hcl

/-- **Along the top side.**  If a vertex `c` of the closed top side of `D` is the vertex at
position `k` of the piece, some vertex of the top side lies to its right, and the right cell is
interior to the piece, then the next vertex `w` to the right on the top side is a neighbour of
position `k`. -/
theorem top_right_nbr (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P) {k : ℕ}
    (hk : k < l.length) {c : ℕ} (hc : l.getD k 0 = c) (hcS : c ∈ sideVtxSet P D.i D.j D.y₂)
    (hex : ∃ j ∈ sideVtxSet P D.i D.j D.y₂, (P.vtx c).1 < (P.vtx j).1)
    (hS : D.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary) :
    ∃ w, w ∈ sideVtxSet P D.i D.j D.y₂ ∧ (P.vtx c).1 < (P.vtx w).1 ∧
      (P.vtx w = (subPoly P l).vtx (prevIdx (subPoly P l) k) ∨
        P.vtx w = (subPoly P l).vtx ((k + 1) % l.length)) := by
  obtain ⟨htmem, htmin⟩ := D.isTrap.topVtx_spec hP D.free
  change ∀ k ∈ sideVtxSet P D.i D.j D.y₂, (P.vtx D.top).1 ≤ (P.vtx k).1 at htmin
  set S : Set ℕ := {j | j ∈ sideVtxSet P D.i D.j D.y₂ ∧ (P.vtx c).1 < (P.vtx j).1} with hSdef
  have hSfin : S.Finite := (sideVtxSet_finite P D.i D.j D.y₂).subset fun _ h => h.1
  have hSne : S.Nonempty := by
    obtain ⟨j, hj, hjc⟩ := hex; exact ⟨j, hj, hjc⟩
  obtain ⟨hmS, hmmin⟩ := leftmostVtx_spec P hSfin hSne
  set w := leftmostVtx P S with hwdef
  have hres := gap_adjacent_or_chord hP (Or.inr rfl) (D.region_subset_interior hP)
    hcS.1 hmS.1.1 hcS.2.1 hmS.1.2.1 hmS.2
    (fun x hx1 hx2 => D.isTrap.near_top (by linarith [hcS.2.2.1]) (by linarith [hmS.1.2.2.2]))
    (fun j hj hjy hj1 hj2 => by
      have hjS : j ∈ S := ⟨⟨hj, hjy, by linarith [hcS.2.2.1], by linarith [hmS.1.2.2.2]⟩, hj1⟩
      linarith [hmmin j hjS])
  have hpe : IsPieceEdge P c w := by
    rcases hres with (h | h) | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
  refine ⟨w, hmS.1, hmS.2, ?_⟩
  have hpe' : IsPieceEdge P (l.getD k 0) w := by rw [hc]; exact hpe
  apply hl.nbr_of_boundary hP hk hmS.1.1 hpe'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  rw [hc]
  have hseg := lerp_mem_segment (P.vtx c) (P.vtx w) hs.1.le hs.2.le
  have hcy := hcS.2.1
  have hwy := hmS.1.2.1
  have hct := htmin c hcS
  have hp : lerp (P.vtx c) (P.vtx w) s =
      (((P.vtx c).1 + s * ((P.vtx w).1 - (P.vtx c).1), D.y₂) : Point) := by
    rw [Geometry.point_ext_iff]
    refine ⟨rfl, ?_⟩
    show (P.vtx c).2 + s * ((P.vtx w).2 - (P.vtx c).2) = D.y₂
    rw [hcy, hwy]; ring
  have h12 : D.y₁ < D.y₂ := D.isTrap.bot_lt.trans D.isTrap.lt_top
  have hx1 : (P.vtx c).1 < (P.vtx c).1 + s * ((P.vtx w).1 - (P.vtx c).1) := by
    nlinarith [hs.1, hmS.2]
  have hx2 : (P.vtx c).1 + s * ((P.vtx w).1 - (P.vtx c).1) ≤ (P.vtx w).1 := by
    nlinarith [hs.2, hmS.2]
  have hcl : lerp (P.vtx c) (P.vtx w) s ∈ closure D.cellR := by
    rw [hp]
    refine D.mem_closure_cellR hP (D.mem_closedTrap_top (by linarith [hcS.2.2.1])
      (by linarith [hmS.1.2.2.2])) (fun _ => ?_)
    rw [D.det_bot_top hP]
    have ht2 := D.top_snd hP
    nlinarith
  exact hl.mem_boundary_of_closure hS hcS.1 hmS.1.1 hpe hseg hcl

/-- **Across the top side, left case.**  If the left cell of `D` is interior to the piece, the
left side edge of `D` is `e`, and the top vertex does not lie on `e`, then the open top side to
the left of the top vertex is a chord through the interior of the piece, and the trapezoid `D'`
above it has left side edge `e`, left cell interior to the piece, and the top vertex of `D` on
its closed bottom side. -/
theorem gap_left (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P) {e : ℕ}
    (he : e < P.n) (heq : D.i = e)
    (hS : D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary)
    (hnot : P.vtx D.top ∉ P.edge e) :
    ∃ D' : TrapData P, D'.i = e ∧
      D'.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary ∧
      D.top ∈ sideVtxSet P D'.i D'.j D'.y₁ := by
  obtain ⟨htmem, htmin⟩ := D.isTrap.topVtx_spec hP D.free
  change D.top ∈ sideVtxSet P D.i D.j D.y₂ at htmem
  change ∀ k ∈ sideVtxSet P D.i D.j D.y₂, (P.vtx D.top).1 ≤ (P.vtx k).1 at htmin
  have hNH : NonHoriz P e := heq ▸ D.isTrap.nhL
  have h12 : D.y₁ < D.y₂ := D.isTrap.bot_lt.trans D.isTrap.lt_top
  set y₂ := D.y₂ with hy₂
  set a := edgeX P e y₂ with ha
  set b := (P.vtx D.top).1 with hb
  have hty : (P.vtx D.top).2 = y₂ := htmem.2.1
  have hab : a < b := by
    refine lt_of_le_of_ne (by rw [ha, ← heq]; exact htmem.2.2.1) (fun h => hnot ?_)
    rw [← heq]
    exact D.isTrap.mem_edgeL (by rw [hty]; exact h12.le) (by rw [hty])
      (by rw [hty, ← hb, ← h, ha, heq])
  have hbj : b ≤ edgeX P D.j y₂ := htmem.2.2.2
  have hnov : ∀ k, k < P.n → (P.vtx k).2 = y₂ → a < (P.vtx k).1 → (P.vtx k).1 < b → False := by
    intro k hk hky hk1 hk2
    have hkS : k ∈ sideVtxSet P D.i D.j y₂ :=
      ⟨hk, hky, by rw [heq]; exact hk1.le, by linarith⟩
    linarith [htmin k hkS]
  have hE : OpenEdgePt P e (a, y₂) := by
    have hmem : ((a, y₂) : Point) ∈ P.edge e := by
      rw [← heq]
      exact D.isTrap.mem_edgeL (p := (a, y₂)) h12.le le_rfl (by rw [ha, heq])
    have hnv : ∀ k, k < P.n → ((a, y₂) : Point) ≠ P.vtx k := by
      intro k hk h
      have h1 : (P.vtx k).1 = a := (congrArg Prod.fst h).symm
      have h2 : (P.vtx k).2 = y₂ := (congrArg Prod.snd h).symm
      have hkS : k ∈ sideVtxSet P D.i D.j y₂ :=
        ⟨hk, h2, by rw [h1, heq], by rw [h1]; linarith⟩
      have := htmin k hkS
      rw [h1] at this
      linarith
    exact openEdgePt_of_mem_edge_ne hmem (hnv e he) (hnv _ (succIdx_lt P he))
  have hgap := fun x (hx1 : a < x) (hx2 : x < b) =>
    D.gap_top hP (a := a) (b := b) (by rw [ha, heq]) hbj hnov he hNH (Or.inl hE) hx1 hx2
  have hint : ∀ x, a < x → x < b →
      ((x, y₂) : Point) ∈ (subPoly P l).filled \ (subPoly P l).boundary := by
    intro x hx1 hx2
    have hcl : ((x, y₂) : Point) ∈ closure D.cellL := by
      refine D.mem_closure_cellL hP (D.mem_closedTrap_top (by rw [heq]; linarith)
        (by linarith)) (fun _ => ?_)
      rw [D.det_bot_top hP]
      simp only
      nlinarith
    refine IsPiece.mem_int_of_closure hS hcl (fun hb' => ?_)
    obtain ⟨h1, -, h3⟩ := hgap x hx1 hx2
    rcases hl.mem_boundary_cases hb' with h | ⟨d, hd, hpd⟩
    · exact h1 h
    · exact h3 d hd hpd
  obtain ⟨D', hy, ha', hb'⟩ := exists_trapData_above hP hab
    (fun x h1 h2 => hl.interior_subset (hint x h1 h2)) (fun x h1 h2 => (hgap x h1 h2).2.1)
  have hi' : D'.i = e :=
    D'.i_eq_of_openEdgePt hP (a := a) (by rw [hy]; exact ha') (by rw [hy]; linarith) he hNH
      (by rw [hy]; exact hE)
  have htS : D.top ∈ sideVtxSet P D'.i D'.j D'.y₁ :=
    ⟨htmem.1, by rw [hy]; exact hty, by rw [hy]; linarith, by rw [hy]; exact hb'⟩
  refine ⟨D', hi', ?_, htS⟩
  obtain ⟨-, hbmax⟩ := D'.isTrap.botVtx_spec hP D'.free
  have htb := hbmax D.top htS
  have hxi := hint ((a + b) / 2) (by linarith) (by linarith)
  rw [← hy] at hxi
  exact D'.cellL_subset_of_bot hP hl (by rw [hy]; linarith) (by rw [hy]; linarith)
    (by change (a + b) / 2 < (P.vtx (botVtx P D'.i D'.j D'.y₁)).1; linarith) hxi

/-- **Across the top side, right case.**  If the right cell of `D` is interior to the piece, the
right side edge of `D` is `e`, and `c` is the rightmost vertex of the closed top side and does not
lie on `e`, then the open top side to the right of `c` is a chord through the interior of the
piece, and the trapezoid `D'` above it has right side edge `e`, right cell interior to the piece,
and bottom vertex `c`. -/
theorem gap_right (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P) {e : ℕ}
    (he : e < P.n) (heq : D.j = e)
    (hS : D.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary) {c : ℕ}
    (hcS : c ∈ sideVtxSet P D.i D.j D.y₂)
    (hmax : ∀ k ∈ sideVtxSet P D.i D.j D.y₂, (P.vtx k).1 ≤ (P.vtx c).1)
    (hnot : P.vtx c ∉ P.edge e) :
    ∃ D' : TrapData P, D'.j = e ∧
      D'.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary ∧ D'.bot = c := by
  obtain ⟨htmem, htmin⟩ := D.isTrap.topVtx_spec hP D.free
  change ∀ k ∈ sideVtxSet P D.i D.j D.y₂, (P.vtx D.top).1 ≤ (P.vtx k).1 at htmin
  have hNH : NonHoriz P e := heq ▸ D.isTrap.nhR
  have h12 : D.y₁ < D.y₂ := D.isTrap.bot_lt.trans D.isTrap.lt_top
  set y₂ := D.y₂ with hy₂
  set a := (P.vtx c).1 with ha
  set b := edgeX P e y₂ with hb
  have hcy : (P.vtx c).2 = y₂ := hcS.2.1
  have hab : a < b := by
    refine lt_of_le_of_ne (by rw [hb, ← heq]; exact hcS.2.2.2) (fun h => hnot ?_)
    rw [← heq]
    exact D.isTrap.mem_edgeR (by rw [hcy]; exact h12.le) (by rw [hcy])
      (by rw [hcy, ← ha, h, hb, heq])
  have hai : edgeX P D.i y₂ ≤ a := hcS.2.2.1
  have hnov : ∀ k, k < P.n → (P.vtx k).2 = y₂ → a < (P.vtx k).1 → (P.vtx k).1 < b → False := by
    intro k hk hky hk1 hk2
    have hkS : k ∈ sideVtxSet P D.i D.j y₂ :=
      ⟨hk, hky, by linarith, by rw [heq]; exact hk2.le⟩
    linarith [hmax k hkS]
  have hbv : ∀ k, k < P.n → ((b, y₂) : Point) ≠ P.vtx k := by
    intro k hk h
    have h1 : (P.vtx k).1 = b := (congrArg Prod.fst h).symm
    have h2 : (P.vtx k).2 = y₂ := (congrArg Prod.snd h).symm
    have hkS : k ∈ sideVtxSet P D.i D.j y₂ :=
      ⟨hk, h2, by rw [h1]; linarith, by rw [h1, hb, heq]⟩
    have := hmax k hkS
    rw [h1] at this
    linarith
  have hE : OpenEdgePt P e (b, y₂) := by
    have hmem : ((b, y₂) : Point) ∈ P.edge e := by
      rw [← heq]
      exact D.isTrap.mem_edgeR (p := (b, y₂)) h12.le le_rfl (by rw [hb, heq])
    exact openEdgePt_of_mem_edge_ne hmem (hbv e he) (hbv _ (succIdx_lt P he))
  have hgap := fun x (hx1 : a < x) (hx2 : x < b) =>
    D.gap_top hP (a := a) (b := b) hai (by rw [hb, heq]) hnov he hNH (Or.inr hE) hx1 hx2
  have hct := htmin c hcS
  have hint : ∀ x, a < x → x < b →
      ((x, y₂) : Point) ∈ (subPoly P l).filled \ (subPoly P l).boundary := by
    intro x hx1 hx2
    have hcl : ((x, y₂) : Point) ∈ closure D.cellR := by
      refine D.mem_closure_cellR hP (D.mem_closedTrap_top (by linarith)
        (by rw [heq]; linarith)) (fun _ => ?_)
      rw [D.det_bot_top hP]
      have ht2 := D.top_snd hP
      simp only
      nlinarith
    refine IsPiece.mem_int_of_closure hS hcl (fun hb' => ?_)
    obtain ⟨h1, -, h3⟩ := hgap x hx1 hx2
    rcases hl.mem_boundary_cases hb' with h | ⟨d, hd, hpd⟩
    · exact h1 h
    · exact h3 d hd hpd
  obtain ⟨D', hy, ha', hb'⟩ := exists_trapData_above hP hab
    (fun x h1 h2 => hl.interior_subset (hint x h1 h2)) (fun x h1 h2 => (hgap x h1 h2).2.1)
  have hj' : D'.j = e :=
    D'.j_eq_of_openEdgePt hP (b := b) (by rw [hy]; linarith) (by rw [hy]; exact hb') he hNH
      (by rw [hy]; exact hE)
  have hcS' : c ∈ sideVtxSet P D'.i D'.j D'.y₁ :=
    ⟨hcS.1, by rw [hy]; exact hcy, by rw [hy]; exact ha', by rw [hy]; linarith⟩
  obtain ⟨hbm, hbmax⟩ := D'.isTrap.botVtx_spec hP D'.free
  change D'.bot ∈ sideVtxSet P D'.i D'.j D'.y₁ at hbm
  change ∀ k ∈ sideVtxSet P D'.i D'.j D'.y₁, (P.vtx k).1 ≤ (P.vtx D'.bot).1 at hbmax
  have hcb := hbmax c hcS'
  have hbot : D'.bot = c := by
    have hby : (P.vtx D'.bot).2 = y₂ := by rw [hbm.2.1, hy]
    have hbj : (P.vtx D'.bot).1 ≤ b := by
      have := hbm.2.2.2; rw [hj', hy] at this; exact this
    have hba : (P.vtx D'.bot).1 = a := by
      by_contra hne
      have hlt : a < (P.vtx D'.bot).1 := lt_of_le_of_ne hcb (Ne.symm hne)
      rcases hbj.lt_or_eq with h | h
      · exact hnov _ hbm.1 hby hlt h
      · exact hbv _ hbm.1 (point_ext h.symm hby.symm)
    exact simple_vtx_inj hP hbm.1 hcS.1 (point_ext (hba.trans ha) (hby.trans hcy.symm))
  refine ⟨D', hj', ?_, hbot⟩
  have hxi := hint ((a + b) / 2) (by linarith) (by linarith)
  rw [← hy] at hxi
  exact D'.cellR_subset_of_bot hP hl (by rw [hy]; linarith) (by rw [hy]; linarith)
    (by rw [hbot]; linarith) hxi

end TrapData

/-! ### The walk states -/

/-- **Left state** of the walk at vertex `c` with base edge `e`: some trapezoid has left side
edge `e`, its left cell interior to the piece, and `c` on its closed bottom side or as its top
vertex. -/
def StateL (P : Polygon) (l : List ℕ) (e c : ℕ) : Prop :=
  ∃ D : TrapData P, D.i = e ∧ D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary ∧
    (c ∈ sideVtxSet P D.i D.j D.y₁ ∨ c = D.top)

/-- **Right state** of the walk at vertex `c` with base edge `e`: some trapezoid has right side
edge `e`, its right cell interior to the piece, and `c` as its bottom vertex or on its closed top
side. -/
def StateR (P : Polygon) (l : List ℕ) (e c : ℕ) : Prop :=
  ∃ D : TrapData P, D.j = e ∧ D.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary ∧
    (c = D.bot ∨ c ∈ sideVtxSet P D.i D.j D.y₂)

/-- The left step from a vertex of the closed bottom side. -/
theorem stateL_step_bot (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P)
    {e : ℕ} (heq : D.i = e) (hS : D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary)
    {k : ℕ} (hk : k < l.length) {c : ℕ} (hc : l.getD k 0 = c)
    (hcS : c ∈ sideVtxSet P D.i D.j D.y₁) :
    ∃ w, w < P.n ∧ StateL P l e w ∧ ylexLT (P.vtx c) (P.vtx w) ∧
      (P.vtx w = (subPoly P l).vtx (prevIdx (subPoly P l) k) ∨
        P.vtx w = (subPoly P l).vtx ((k + 1) % l.length)) := by
  by_cases hcb : c = D.bot
  · refine ⟨D.top, D.top_lt hP, ⟨D, heq, hS, Or.inr rfl⟩, ?_,
      D.bot_top_nbr hP hl hk (hc.trans hcb) (Or.inl hS)⟩
    apply ylexLT_of_snd_lt
    rw [hcS.2.1, D.top_snd hP]
    exact D.isTrap.bot_lt.trans D.isTrap.lt_top
  · obtain ⟨w, hw, hcw, hnb⟩ := D.bot_right_nbr hP hl hk hc hcS hcb hS
    exact ⟨w, hw.1, ⟨D, heq, hS, Or.inl hw⟩, Or.inr ⟨hcS.2.1.trans hw.2.1.symm, hcw⟩, hnb⟩

/-- **The left step.**  A vertex of the piece in the left state, not on the base edge, has a
neighbour in the piece which is strictly `ylexLT`-above it and again in the left state. -/
theorem StateL.step (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) {e : ℕ} (he : e < P.n)
    {k : ℕ} (hk : k < l.length) {c : ℕ} (hc : l.getD k 0 = c) (hst : StateL P l e c)
    (hnot : P.vtx c ∉ P.edge e) :
    ∃ w, w < P.n ∧ StateL P l e w ∧ ylexLT (P.vtx c) (P.vtx w) ∧
      (P.vtx w = (subPoly P l).vtx (prevIdx (subPoly P l) k) ∨
        P.vtx w = (subPoly P l).vtx ((k + 1) % l.length)) := by
  obtain ⟨D, heq, hS, hc'⟩ := hst
  rcases hc' with hcS | rfl
  · exact stateL_step_bot hP hl D heq hS hk hc hcS
  · obtain ⟨D', hi', hS', htS⟩ := D.gap_left hP hl he heq hS hnot
    exact stateL_step_bot hP hl D' hi' hS' hk hc htS

/-- **The right step.**  A vertex of the piece in the right state, not on the base edge, has a
neighbour in the piece which is strictly `ylexLT`-above it and again in the right state. -/
theorem StateR.step (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) {e : ℕ} (he : e < P.n)
    {k : ℕ} (hk : k < l.length) {c : ℕ} (hc : l.getD k 0 = c) (hst : StateR P l e c)
    (hnot : P.vtx c ∉ P.edge e) :
    ∃ w, w < P.n ∧ StateR P l e w ∧ ylexLT (P.vtx c) (P.vtx w) ∧
      (P.vtx w = (subPoly P l).vtx (prevIdx (subPoly P l) k) ∨
        P.vtx w = (subPoly P l).vtx ((k + 1) % l.length)) := by
  obtain ⟨D, heq, hS, hc'⟩ := hst
  rcases hc' with rfl | hcS
  · refine ⟨D.top, D.top_lt hP, ⟨D, heq, hS, Or.inr (D.isTrap.topVtx_mem hP D.free)⟩, ?_,
      D.bot_top_nbr hP hl hk hc (Or.inr hS)⟩
    exact ylexLT_of_snd_lt (D.bot_snd_lt_top_snd hP)
  · by_cases hex : ∃ j ∈ sideVtxSet P D.i D.j D.y₂, (P.vtx c).1 < (P.vtx j).1
    · obtain ⟨w, hw, hcw, hnb⟩ := D.top_right_nbr hP hl hk hc hcS hex hS
      exact ⟨w, hw.1, ⟨D, heq, hS, Or.inr hw⟩, Or.inr ⟨hcS.2.1.trans hw.2.1.symm, hcw⟩, hnb⟩
    · push Not at hex
      obtain ⟨D', hj', hS', hbot⟩ := D.gap_right hP hl he heq hS hcS hex hnot
      refine ⟨D'.top, D'.top_lt hP, ⟨D', hj', hS', Or.inr (D'.isTrap.topVtx_mem hP D'.free)⟩, ?_,
        D'.bot_top_nbr hP hl hk (hc.trans hbot.symm) (Or.inr hS')⟩
      rw [← hbot]
      exact ylexLT_of_snd_lt (D'.bot_snd_lt_top_snd hP)

end

end Chazelle.Mountain
