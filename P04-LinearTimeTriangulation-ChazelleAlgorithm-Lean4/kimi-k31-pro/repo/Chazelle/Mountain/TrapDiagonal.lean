module

public import Chazelle.Visibility.Trapezoid
public import Chazelle.Existence.Diagonal
public import Chazelle.Mountain.Lex
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# The top and bottom vertices of a trapezoid, and its diagonal

Let `hT : IsTrap P q i j y₁ y₂` be the trapezoid data of a free point `q` of a simple polygon
`P` (`Chazelle.Visibility.Trapezoid`).  The closed top side of the trapezoid is the horizontal
segment `[edgeX P i y₂, edgeX P j y₂] × {y₂}`, the closed bottom side is
`[edgeX P i y₁, edgeX P j y₁] × {y₁}`; each carries at least one vertex of `P`
(`IsTrap.top_vertex`, `IsTrap.bot_vertex`, once `edgeX_le_top`/`edgeX_le_bot` show that the
sides are not reversed).

## Tie-break conventions

* `ylexLT p q := p.2 < q.2 ∨ (p.2 = q.2 ∧ p.1 < q.1)` is the `(y, x)`-lexicographic order.
* `sideVtxSet P i j y` is the set of vertex indices at height `y` on the closed segment between
  the two side lines.
* The **top vertex** `topVtx P i j y₂` is the `ylexLT`-*minimal* (= leftmost) vertex of
  `sideVtxSet P i j y₂`; the **bottom vertex** `botVtx P i j y₁` is the `ylexLT`-*maximal*
  (= rightmost) vertex of `sideVtxSet P i j y₁`.  (These are the vertices found by a downward,
  respectively upward, sweep in the `ylexLT`-perturbed picture: the middle slab of the
  perturbed trapezoid has exactly these two as its top and bottom vertices.)
  Both are defined for all `P i j y` through `Classical.epsilon`; the specification lemmas need
  the trapezoid data (`IsTrap.topVtx_mem`, `IsTrap.botVtx_mem`, …).

## Main results

* `IsTrap.edgeX_le_top`, `IsTrap.edgeX_le_bot`: the side lines do not cross inside the
  trapezoid's height range, so `edgeX P i y₂ ≤ edgeX P j y₂` and `edgeX P i y₁ ≤ edgeX P j y₁`;
  `IsTrap.edgeX_lt`: strictly between the heights the order is strict.
* `IsTrap.topVtx_ne_botVtx`: the two vertices differ.
* `IsTrap.diag_lerp_mem_closedTrap`: the segment between them lies in the closed trapezoid;
  `IsTrap.diag_lerp_mem_trapSet`: if they are **not adjacent** in `P`, the open segment lies
  in the open trapezoid, hence (`IsTrap.exists_isDiagonal`) it is an interior diagonal in the
  sense of `Chazelle.Existence.IsDiagonal`, with the closed segment inside `P.filled`.
* `IsTrap.top_eq_side_of_adjacent`, `IsTrap.bot_eq_side_of_adjacent`: if they are adjacent,
  the edge joining them is the left or the right side edge `i` or `j`.
* `IsTrap.vtx_mem_closedTrap_iff`: every vertex of `P` in the closed trapezoid lies on the
  closed top or bottom side.
* `IsTrap.topVtx_eq_of_trapSet_eq`: the top and bottom vertices depend only on the region
  (open trapezoid), not on the particular data `q i j y₁ y₂` describing it.
-/

namespace Chazelle.Mountain

@[expose] public section

open Set Filter Topology
open Chazelle.Jordan
open Chazelle.Visibility
open Chazelle.Existence (IsDiagonal eq_endpoint_of_vtx_mem_edge vtx_mem_boundary)
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one point_ext point_ext_iff
  lerp_mem_segment)

/-! ### The `(y, x)`-lexicographic order -/

/-! ### Vertices on a horizontal side -/

/-- The vertices of `P` at height `y` on the closed horizontal segment between the line of
edge `i` and the line of edge `j`. -/
def sideVtxSet (P : Polygon) (i j : ℕ) (y : ℝ) : Set ℕ :=
  {k | k < P.n ∧ (P.vtx k).2 = y ∧ edgeX P i y ≤ (P.vtx k).1 ∧ (P.vtx k).1 ≤ edgeX P j y}

theorem sideVtxSet_finite (P : Polygon) (i j : ℕ) (y : ℝ) : (sideVtxSet P i j y).Finite :=
  (Set.finite_lt_nat P.n).subset fun _ hk => hk.1

/-- The vertex of smallest abscissa in a set of indices (`0` if the set is empty or infinite). -/
noncomputable def leftmostVtx (P : Polygon) (S : Set ℕ) : ℕ :=
  Classical.epsilon fun k => k ∈ S ∧ ∀ k' ∈ S, (P.vtx k).1 ≤ (P.vtx k').1

/-- The vertex of largest abscissa in a set of indices (`0` if the set is empty or infinite). -/
noncomputable def rightmostVtx (P : Polygon) (S : Set ℕ) : ℕ :=
  Classical.epsilon fun k => k ∈ S ∧ ∀ k' ∈ S, (P.vtx k').1 ≤ (P.vtx k).1

theorem leftmostVtx_spec (P : Polygon) {S : Set ℕ} (hfin : S.Finite) (hne : S.Nonempty) :
    leftmostVtx P S ∈ S ∧ ∀ k' ∈ S, (P.vtx (leftmostVtx P S)).1 ≤ (P.vtx k').1 :=
  Classical.epsilon_spec (p := fun k => k ∈ S ∧ ∀ k' ∈ S, (P.vtx k).1 ≤ (P.vtx k').1)
    (by
      obtain ⟨a, ha, h⟩ := Set.exists_min_image S (fun k => (P.vtx k).1) hfin hne
      exact ⟨a, ha, h⟩)

theorem rightmostVtx_spec (P : Polygon) {S : Set ℕ} (hfin : S.Finite) (hne : S.Nonempty) :
    rightmostVtx P S ∈ S ∧ ∀ k' ∈ S, (P.vtx k').1 ≤ (P.vtx (rightmostVtx P S)).1 :=
  Classical.epsilon_spec (p := fun k => k ∈ S ∧ ∀ k' ∈ S, (P.vtx k').1 ≤ (P.vtx k).1)
    (by
      obtain ⟨a, ha, h⟩ := Set.exists_max_image S (fun k => (P.vtx k).1) hfin hne
      exact ⟨a, ha, h⟩)

/-- **The top vertex** of the trapezoid with side edges `i`, `j` and top height `y`: the
leftmost (= `ylexLT`-minimal) vertex of the closed top side. -/
noncomputable def topVtx (P : Polygon) (i j : ℕ) (y : ℝ) : ℕ := leftmostVtx P (sideVtxSet P i j y)

/-- **The bottom vertex** of the trapezoid with side edges `i`, `j` and bottom height `y`: the
rightmost (= `ylexLT`-maximal) vertex of the closed bottom side. -/
noncomputable def botVtx (P : Polygon) (i j : ℕ) (y : ℝ) : ℕ := rightmostVtx P (sideVtxSet P i j y)

/-! ### Affine bookkeeping -/

/-- The abscissa of the line of edge `i` at the height of a point of the segment `a b`. -/
theorem edgeX_lerp_snd (P : Polygon) (i : ℕ) (a b : Point) (s : ℝ) :
    edgeX P i (lerp a b s).2 = (1 - s) * edgeX P i a.2 + s * edgeX P i b.2 := by
  rw [← edgeX_combo P i (by ring : (1 - s) + s = 1)]
  congr 1
  rwring [lerp_snd]

/-- For a valid diagonal `(t, b)` (indices in range, distinct, non-adjacent), the arc length
`L` from `t` to `b` satisfies `2 ≤ L ≤ n - 2` and `(t + L) % n = b`. -/
theorem exists_diag_index {P : Polygon} (hn : 3 ≤ P.n) {t b : ℕ} (ht : t < P.n) (hb : b < P.n)
    (htb : t ≠ b) (h1 : b ≠ (t + 1) % P.n) (h2 : t ≠ (b + 1) % P.n) :
    ∃ L, 2 ≤ L ∧ L + 2 ≤ P.n ∧ (t + L) % P.n = b := by
  rw [succIdx_eq P ht] at h1
  rw [succIdx_eq P hb] at h2
  rcases le_or_gt t b with hle | hlt
  · refine ⟨b - t, ?_, ?_, ?_⟩
    · split_ifs at h1 h2 <;> omega
    · split_ifs at h1 h2 <;> omega
    · rw [Nat.add_sub_cancel' hle]; exact Nat.mod_eq_of_lt hb
  · refine ⟨b + P.n - t, ?_, ?_, ?_⟩
    · split_ifs at h1 h2 <;> omega
    · split_ifs at h1 h2 <;> omega
    · rw [show t + (b + P.n - t) = b + P.n by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt hb

/-! ### The side lines do not cross -/

end

end Chazelle.Mountain

namespace Chazelle.Visibility.IsTrap

@[expose] public section

open Set Filter Topology
open Chazelle.Jordan
open Chazelle.Mountain
open Chazelle.Existence (IsDiagonal eq_endpoint_of_vtx_mem_edge vtx_mem_boundary)
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one point_ext point_ext_iff
  lerp_mem_segment)

variable {P : Polygon} {q : Point} {i j : ℕ} {y₁ y₂ : ℝ}

/-- **The top side is not reversed**: `edgeX P i y₂ ≤ edgeX P j y₂`.  (Otherwise the two side
lines would cross at a height in `(q.2, y₂)`; the crossing point lies on both edges, so it is a
common vertex, inside the corridor, contradicting `no_vertex`.) -/
theorem edgeX_le_top (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    edgeX P i y₂ ≤ edgeX P j y₂ := by
  by_contra hlt
  rw [not_le] at hlt
  have hq' := hT.q_mem hP hq.1
  have hcont : ContinuousOn (fun y => edgeX P j y - edgeX P i y) (Icc q.2 y₂) :=
    ((continuous_edgeX P j).sub (continuous_edgeX P i)).continuousOn
  have h0 : (0 : ℝ) ∈ Ioo (edgeX P j y₂ - edgeX P i y₂) (edgeX P j q.2 - edgeX P i q.2) :=
    ⟨by linarith, by linarith [hq'.2.2.1, hq'.2.2.2]⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Ioo' hT.lt_top.le hcont h0
  have hfy'  := hfy
  have hb := hT.bot_lt
  have hzi : ((edgeX P i y, y) : Point) ∈ P.edge i :=
    hT.mem_edgeL (by show y₁ ≤ y; linarith [hy.1]) (by show y ≤ y₂; exact hy.2.le) rfl
  have hzj : ((edgeX P i y, y) : Point) ∈ P.edge j :=
    hT.mem_edgeR (by show y₁ ≤ y; linarith [hy.1]) (by show y ≤ y₂; exact hy.2.le)
      (by show edgeX P i y = edgeX P j y; linarith)
  rcases simple_endpoint_of_mem_two hP hT.hi hT.hj (hT.ne hP hq.1) hzi hzj with hz | hz
  · have h := hT.no_vertex i hT.hi
    rw [← hz] at h
    exact h (by show y₁ < y; linarith [hy.1]) hy.2 le_rfl
      (by show edgeX P i y ≤ edgeX P j y; linarith)
  · have h := hT.no_vertex _ (succIdx_lt P hT.hi)
    rw [← hz] at h
    exact h (by show y₁ < y; linarith [hy.1]) hy.2 le_rfl
      (by show edgeX P i y ≤ edgeX P j y; linarith)

/-- **The bottom side is not reversed**: `edgeX P i y₁ ≤ edgeX P j y₁`. -/
theorem edgeX_le_bot (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    edgeX P i y₁ ≤ edgeX P j y₁ := by
  by_contra hlt
  rw [not_le] at hlt
  have hq' := hT.q_mem hP hq.1
  have hcont : ContinuousOn (fun y => edgeX P j y - edgeX P i y) (Icc y₁ q.2) :=
    ((continuous_edgeX P j).sub (continuous_edgeX P i)).continuousOn
  have h0 : (0 : ℝ) ∈ Ioo (edgeX P j y₁ - edgeX P i y₁) (edgeX P j q.2 - edgeX P i q.2) :=
    ⟨by linarith, by linarith [hq'.2.2.1, hq'.2.2.2]⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Ioo hT.bot_lt.le hcont h0
  have hfy'  := hfy
  have ht := hT.lt_top
  have hzi : ((edgeX P i y, y) : Point) ∈ P.edge i :=
    hT.mem_edgeL (by show y₁ ≤ y; exact hy.1.le) (by show y ≤ y₂; linarith [hy.2]) rfl
  have hzj : ((edgeX P i y, y) : Point) ∈ P.edge j :=
    hT.mem_edgeR (by show y₁ ≤ y; exact hy.1.le) (by show y ≤ y₂; linarith [hy.2])
      (by show edgeX P i y = edgeX P j y; linarith)
  rcases simple_endpoint_of_mem_two hP hT.hi hT.hj (hT.ne hP hq.1) hzi hzj with hz | hz
  · have h := hT.no_vertex i hT.hi
    rw [← hz] at h
    exact h hy.1 (by show y < y₂; linarith [hy.2]) le_rfl
      (by show edgeX P i y ≤ edgeX P j y; linarith)
  · have h := hT.no_vertex _ (succIdx_lt P hT.hi)
    rw [← hz] at h
    exact h hy.1 (by show y < y₂; linarith [hy.2]) le_rfl
      (by show edgeX P i y ≤ edgeX P j y; linarith)

/-- Strictly between the two heights, the left side line is strictly left of the right one. -/
theorem edgeX_lt (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) {y : ℝ}
    (h1 : y₁ < y) (h2 : y < y₂) : edgeX P i y < edgeX P j y := by
  have hq' := hT.q_mem hP hq.1
  have hqlt  := hq'.2.2.1.trans hq'.2.2.2
  have hb := hT.edgeX_le_bot hP hq
  have ht := hT.edgeX_le_top hP hq
  have h12 := hT.bot_lt
  have h23 := hT.lt_top
  rcases le_or_gt y q.2 with hle | hlt
  · obtain ⟨l, hl0, hl1, hy⟩ : ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ y = (1 - l) * y₁ + l * q.2 := by
      refine ⟨(y - y₁) / (q.2 - y₁), div_pos (by linarith) (by linarith), ?_, ?_⟩
      · rwli [div_le_one (by linarith)]
      · have hne : q.2 - y₁ ≠ 0 := by linarith
        field_simp
        ring
    rw [hy, edgeX_combo P i (by ring), edgeX_combo P j (by ring)]
    have e1 := mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 hb)
    have e2 := mul_pos hl0 (sub_pos.2 hqlt)
    linarith
  · obtain ⟨l, hl0, hl1, hy⟩ : ∃ l : ℝ, 0 ≤ l ∧ l < 1 ∧ y = (1 - l) * q.2 + l * y₂ := by
      refine ⟨(y - q.2) / (y₂ - q.2), div_nonneg (by linarith) (by linarith), ?_, ?_⟩
      · rwli [div_lt_one (by linarith)]
      · have hne : y₂ - q.2 ≠ 0 := by linarith
        field_simp
        ring
    rw [hy, edgeX_combo P i (by ring), edgeX_combo P j (by ring)]
    have e1 := mul_pos (sub_pos.2 hl1) (sub_pos.2 hqlt)
    have e2 := mul_nonneg hl0 (sub_nonneg.2 ht)
    linarith

/-- The midpoint of the horizontal section at a height strictly between the two heights lies in
the trapezoid. -/
theorem mid_mem_trapSet (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    {y : ℝ} (h1 : y₁ < y) (h2 : y < y₂) :
    (((edgeX P i y + edgeX P j y) / 2, y) : Point) ∈ trapSet P i j y₁ y₂ := by
  have := hT.edgeX_lt hP hq h1 h2
  exact ⟨h1, h2, by show edgeX P i y < (edgeX P i y + edgeX P j y) / 2; linarith,
    by show (edgeX P i y + edgeX P j y) / 2 < edgeX P j y; linarith⟩

/-! ### The top and bottom vertices -/

theorem sideVtxSet_top_nonempty (hP : P.Simple) (hq : q ∈ freeRegion P)
    (hT : IsTrap P q i j y₁ y₂) : (sideVtxSet P i j y₂).Nonempty := by
  obtain ⟨k, hk, hky, hkx⟩ := hT.top_vertex
  obtain ⟨h1, h2⟩ := hkx (hT.edgeX_le_top hP hq)
  exact ⟨k, hk, hky, h1, h2⟩

theorem sideVtxSet_bot_nonempty (hP : P.Simple) (hq : q ∈ freeRegion P)
    (hT : IsTrap P q i j y₁ y₂) : (sideVtxSet P i j y₁).Nonempty := by
  obtain ⟨k, hk, hky, hkx⟩ := hT.bot_vertex
  obtain ⟨h1, h2⟩ := hkx (hT.edgeX_le_bot hP hq)
  exact ⟨k, hk, hky, h1, h2⟩

/-- The top vertex is a vertex of the closed top side, and the leftmost one. -/
theorem topVtx_spec (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    topVtx P i j y₂ ∈ sideVtxSet P i j y₂ ∧
      ∀ k ∈ sideVtxSet P i j y₂, (P.vtx (topVtx P i j y₂)).1 ≤ (P.vtx k).1 :=
  leftmostVtx_spec P (sideVtxSet_finite P i j y₂) (hT.sideVtxSet_top_nonempty hP hq)

/-- The bottom vertex is a vertex of the closed bottom side, and the rightmost one. -/
theorem botVtx_spec (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    botVtx P i j y₁ ∈ sideVtxSet P i j y₁ ∧
      ∀ k ∈ sideVtxSet P i j y₁, (P.vtx k).1 ≤ (P.vtx (botVtx P i j y₁)).1 :=
  rightmostVtx_spec P (sideVtxSet_finite P i j y₁) (hT.sideVtxSet_bot_nonempty hP hq)

theorem topVtx_mem (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    topVtx P i j y₂ ∈ sideVtxSet P i j y₂ := (hT.topVtx_spec hP hq).1

theorem botVtx_mem (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    botVtx P i j y₁ ∈ sideVtxSet P i j y₁ := (hT.botVtx_spec hP hq).1

theorem topVtx_lt (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    topVtx P i j y₂ < P.n := (hT.topVtx_mem hP hq).1

theorem botVtx_lt (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    botVtx P i j y₁ < P.n := (hT.botVtx_mem hP hq).1

/-- The top vertex is at the top height. -/
theorem topVtx_snd (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    (P.vtx (topVtx P i j y₂)).2 = y₂ := (hT.topVtx_mem hP hq).2.1

/-- The bottom vertex is at the bottom height. -/
theorem botVtx_snd (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    (P.vtx (botVtx P i j y₁)).2 = y₁ := (hT.botVtx_mem hP hq).2.1

/-- **The top and bottom vertices are distinct** (their heights differ). -/
theorem topVtx_ne_botVtx (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    topVtx P i j y₂ ≠ botVtx P i j y₁ := by
  intro h
  have h1 := hT.topVtx_snd hP hq
  have h2 := hT.botVtx_snd hP hq
  rw [h] at h1
  linarith [hT.bot_lt, hT.lt_top]

/-- The bottom vertex is strictly below the top vertex. -/
theorem botVtx_snd_lt (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    (P.vtx (botVtx P i j y₁)).2 < (P.vtx (topVtx P i j y₂)).2 := by
  rw [hT.topVtx_snd hP hq, hT.botVtx_snd hP hq]
  exact hT.bot_lt.trans hT.lt_top

/-! ### The segment from the top vertex to the bottom vertex -/

/-- The segment between the top and bottom vertices lies in the closed trapezoid. -/
theorem diag_lerp_mem_closedTrap (hP : P.Simple) (hq : q ∈ freeRegion P)
    (hT : IsTrap P q i j y₁ y₂) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    lerp (P.vtx (topVtx P i j y₂)) (P.vtx (botVtx P i j y₁)) s ∈ closedTrap P i j y₁ y₂ := by
  have hTy := hT.topVtx_snd hP hq
  have hBy := hT.botVtx_snd hP hq
  obtain ⟨-, -, hTi, hTj⟩ := hT.topVtx_mem hP hq
  obtain ⟨-, -, hBi, hBj⟩ := hT.botVtx_mem hP hq
  have h12 := hT.bot_lt.trans hT.lt_top
  refine ⟨?_, ?_, ?_, ?_⟩
  · show y₁ ≤ (lerp _ _ s).2
    rwnl [lerp_snd, hTy, hBy]
  · show (lerp _ _ s).2 ≤ y₂
    rwnl [lerp_snd, hTy, hBy]
  · show edgeX P i (lerp _ _ s).2 ≤ (lerp _ _ s).1
    rw [edgeX_lerp_snd, lerp_fst, hTy, hBy]
    have e1 := mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hTi)
    have e2 := mul_nonneg hs0 (sub_nonneg.2 hBi)
    linarith
  · show (lerp _ _ s).1 ≤ edgeX P j (lerp _ _ s).2
    rw [edgeX_lerp_snd, lerp_fst, hTy, hBy]
    have e1 := mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hTj)
    have e2 := mul_nonneg hs0 (sub_nonneg.2 hBj)
    linarith

/-- If the top and bottom vertices are not adjacent in `P`, they do not both lie on the line
of the left side edge `i` (else they would be the two endpoints of edge `i`). -/
theorem not_both_on_left (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    (h1 : botVtx P i j y₁ ≠ (topVtx P i j y₂ + 1) % P.n)
    (h2 : topVtx P i j y₂ ≠ (botVtx P i j y₁ + 1) % P.n) :
    ¬ ((P.vtx (topVtx P i j y₂)).1 = edgeX P i y₂ ∧ (P.vtx (botVtx P i j y₁)).1 = edgeX P i y₁) := by
  rintro ⟨hT1, hB1⟩
  have ht := hT.topVtx_lt hP hq
  have hb := hT.botVtx_lt hP hq
  have hTy := hT.topVtx_snd hP hq
  have hBy := hT.botVtx_snd hP hq
  have h12 := (hT.bot_lt.trans hT.lt_top).le
  have hTe : P.vtx (topVtx P i j y₂) ∈ P.edge i :=
    hT.mem_edgeL (by rwx [hTy]) (by rw [hTy]) (by rwx [hTy])
  have hBe : P.vtx (botVtx P i j y₁) ∈ P.edge i :=
    hT.mem_edgeL (by rw [hBy]) (by rwx [hBy]) (by rwx [hBy])
  have hne := hT.topVtx_ne_botVtx hP hq
  have hsucc := succIdx_lt P hT.hi
  rcases eq_endpoint_of_vtx_mem_edge hP ht hT.hi hTe with e1 | e1 <;>
    rcases eq_endpoint_of_vtx_mem_edge hP hb hT.hi hBe with e2 | e2
  · exact hne ((simple_vtx_inj hP ht hT.hi e1).trans (simple_vtx_inj hP hb hT.hi e2).symm)
  · have f1 := simple_vtx_inj hP ht hT.hi e1
    have f2 := simple_vtx_inj hP hb hsucc e2
    exact h1 (by rw [f2, f1])
  · have f1 := simple_vtx_inj hP ht hsucc e1
    have f2 := simple_vtx_inj hP hb hT.hi e2
    exact h2 (by rw [f1, f2])
  · exact hne ((simple_vtx_inj hP ht hsucc e1).trans (simple_vtx_inj hP hb hsucc e2).symm)

/-- If the top and bottom vertices are not adjacent in `P`, they do not both lie on the line
of the right side edge `j`. -/
theorem not_both_on_right (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    (h1 : botVtx P i j y₁ ≠ (topVtx P i j y₂ + 1) % P.n)
    (h2 : topVtx P i j y₂ ≠ (botVtx P i j y₁ + 1) % P.n) :
    ¬ ((P.vtx (topVtx P i j y₂)).1 = edgeX P j y₂ ∧ (P.vtx (botVtx P i j y₁)).1 = edgeX P j y₁) := by
  rintro ⟨hT1, hB1⟩
  have ht := hT.topVtx_lt hP hq
  have hb := hT.botVtx_lt hP hq
  have hTy := hT.topVtx_snd hP hq
  have hBy := hT.botVtx_snd hP hq
  have h12 := (hT.bot_lt.trans hT.lt_top).le
  have hTe : P.vtx (topVtx P i j y₂) ∈ P.edge j :=
    hT.mem_edgeR (by rwx [hTy]) (by rw [hTy]) (by rwx [hTy])
  have hBe : P.vtx (botVtx P i j y₁) ∈ P.edge j :=
    hT.mem_edgeR (by rw [hBy]) (by rwx [hBy]) (by rwx [hBy])
  have hne := hT.topVtx_ne_botVtx hP hq
  have hsucc := succIdx_lt P hT.hj
  rcases eq_endpoint_of_vtx_mem_edge hP ht hT.hj hTe with e1 | e1 <;>
    rcases eq_endpoint_of_vtx_mem_edge hP hb hT.hj hBe with e2 | e2
  · exact hne ((simple_vtx_inj hP ht hT.hj e1).trans (simple_vtx_inj hP hb hT.hj e2).symm)
  · have f1 := simple_vtx_inj hP ht hT.hj e1
    have f2 := simple_vtx_inj hP hb hsucc e2
    exact h1 (by rw [f2, f1])
  · have f1 := simple_vtx_inj hP ht hsucc e1
    have f2 := simple_vtx_inj hP hb hT.hj e2
    exact h2 (by rw [f1, f2])
  · exact hne ((simple_vtx_inj hP ht hsucc e1).trans (simple_vtx_inj hP hb hsucc e2).symm)

/-- **The open diagonal lies in the open trapezoid** when the top and bottom vertices are not
adjacent in `P`. -/
theorem diag_lerp_mem_trapSet (hP : P.Simple) (hq : q ∈ freeRegion P)
    (hT : IsTrap P q i j y₁ y₂) (h1 : botVtx P i j y₁ ≠ (topVtx P i j y₂ + 1) % P.n)
    (h2 : topVtx P i j y₂ ≠ (botVtx P i j y₁ + 1) % P.n) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    lerp (P.vtx (topVtx P i j y₂)) (P.vtx (botVtx P i j y₁)) s ∈ trapSet P i j y₁ y₂ := by
  have hTy := hT.topVtx_snd hP hq
  have hBy := hT.botVtx_snd hP hq
  obtain ⟨-, -, hTi, hTj⟩ := hT.topVtx_mem hP hq
  obtain ⟨-, -, hBi, hBj⟩ := hT.botVtx_mem hP hq
  have h12 := hT.bot_lt.trans hT.lt_top
  have hnotL := hT.not_both_on_left hP hq h1 h2
  have hnotR := hT.not_both_on_right hP hq h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · show y₁ < (lerp _ _ s).2
    rwnl [lerp_snd, hTy, hBy]
  · show (lerp _ _ s).2 < y₂
    rwnl [lerp_snd, hTy, hBy]
  · show edgeX P i (lerp _ _ s).2 < (lerp _ _ s).1
    rw [edgeX_lerp_snd, lerp_fst, hTy, hBy]
    rcases lt_or_eq_of_le hTi with hlt | heq
    · have e1 := mul_pos (sub_pos.2 hs1) (sub_pos.2 hlt)
      have e2 := mul_nonneg hs0.le (sub_nonneg.2 hBi)
      linarith
    · have hlt' : edgeX P i y₁ < (P.vtx (botVtx P i j y₁)).1 :=
        lt_of_le_of_ne hBi (fun e => hnotL ⟨heq.symm, e.symm⟩)
      have e1 := mul_nonneg (sub_nonneg.2 hs1.le) (sub_nonneg.2 hTi)
      have e2 := mul_pos hs0 (sub_pos.2 hlt')
      linarith
  · show (lerp _ _ s).1 < edgeX P j (lerp _ _ s).2
    rw [edgeX_lerp_snd, lerp_fst, hTy, hBy]
    rcases lt_or_eq_of_le hTj with hlt | heq
    · have e1 := mul_pos (sub_pos.2 hs1) (sub_pos.2 hlt)
      have e2 := mul_nonneg hs0.le (sub_nonneg.2 hBj)
      linarith
    · have hlt' : (P.vtx (botVtx P i j y₁)).1 < edgeX P j y₁ :=
        lt_of_le_of_ne hBj (fun e => hnotR ⟨heq, e⟩)
      have e1 := mul_nonneg (sub_nonneg.2 hs1.le) (sub_nonneg.2 hTj)
      have e2 := mul_pos hs0 (sub_pos.2 hlt')
      linarith

/-- A point of the closed diagonal (non-adjacent case) is an endpoint or lies in the open
trapezoid. -/
theorem diag_segment_cases (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    (h1 : botVtx P i j y₁ ≠ (topVtx P i j y₂ + 1) % P.n)
    (h2 : topVtx P i j y₂ ≠ (botVtx P i j y₁ + 1) % P.n) {p : Point}
    (hp : p ∈ Chazelle.segment (P.vtx (topVtx P i j y₂)) (P.vtx (botVtx P i j y₁))) :
    p = P.vtx (topVtx P i j y₂) ∨ p = P.vtx (botVtx P i j y₁) ∨ p ∈ trapSet P i j y₁ y₂ := by
  obtain ⟨s, hs0, hs1, rfl⟩ := hp
  rcases hs0.lt_or_eq with hs0 | rfl
  · rcases hs1.lt_or_eq with hs1 | rfl
    · exact Or.inr (Or.inr (hT.diag_lerp_mem_trapSet hP hq h1 h2 hs0 hs1))
    · exact Or.inr (Or.inl (lerp_one _ _))
  · exact Or.inl (lerp_zero _ _)

/-- **The diagonal lemma.**  If the top and bottom vertices of a trapezoid are not adjacent in
`P`, the segment between them is an interior diagonal: `IsDiagonal P s L` with
`s % n = topVtx`, `(s + L) % n = botVtx`, and the closed segment lies in the filled region. -/
theorem exists_isDiagonal (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    (h1 : botVtx P i j y₁ ≠ (topVtx P i j y₂ + 1) % P.n)
    (h2 : topVtx P i j y₂ ≠ (botVtx P i j y₁ + 1) % P.n) :
    ∃ s L, IsDiagonal P s L ∧ s % P.n = topVtx P i j y₂ ∧ (s + L) % P.n = botVtx P i j y₁ ∧
      Chazelle.segment (P.vtx (topVtx P i j y₂)) (P.vtx (botVtx P i j y₁)) ⊆ P.filled := by
  have ht := hT.topVtx_lt hP hq
  have hb := hT.botVtx_lt hP hq
  have hne := hT.topVtx_ne_botVtx hP hq
  obtain ⟨L, hL2, hLn, hsL⟩ := exists_diag_index (simple_three_le hP) ht hb hne h1 h2
  have hs  := Nat.mod_eq_of_lt ht
  refine ⟨topVtx P i j y₂, L, ⟨hL2, hLn, ?_⟩, hs, hsL, ?_⟩
  · rw [hs, hsL]
    intro p hp hpT hpB
    rcases hT.diag_segment_cases hP hq h1 h2 hp with e | e | hin
    · exact absurd e hpT
    · exact absurd e hpB
    · exact hT.not_mem_boundary hP hq hin
  · intro p hp
    rcases hT.diag_segment_cases hP hq h1 h2 hp with rfl | rfl | hin
    · exact boundary_subset_filled P (vtx_mem_boundary P ht)
    · exact boundary_subset_filled P (vtx_mem_boundary P hb)
    · exact (hT.trapSet_subset_interior hP hq hin).1

/-! ### The adjacent case: the diagonal is a side edge -/

/-! ### Vertices of the closed trapezoid -/

/-- **Every vertex of `P` in the closed trapezoid lies on the closed top or bottom side.** -/
theorem vtx_mem_closedTrap_iff (hT : IsTrap P q i j y₁ y₂) {k : ℕ} (hk : k < P.n) :
    P.vtx k ∈ closedTrap P i j y₁ y₂ ↔ k ∈ sideVtxSet P i j y₁ ∨ k ∈ sideVtxSet P i j y₂ := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · exact (hT.no_vertex k hk h1 h2 h3 h4).elim
      · right
        refine ⟨hk, h2, ?_, ?_⟩ <;> rw [← h2] <;> assumption
    · left
      refine ⟨hk, h1.symm, ?_, ?_⟩ <;> rw [h1] <;> assumption
  · have h12 := (hT.bot_lt.trans hT.lt_top).le
    rintro (⟨-, hy, h3, h4⟩ | ⟨-, hy, h3, h4⟩)
    · exact ⟨hy.ge, by rwx [hy], by rwx [hy], by rwx [hy]⟩
    · exact ⟨by rwx [hy], hy.le, by rwx [hy], by rwx [hy]⟩

/-- A vertex of `P` in the closure of the trapezoid lies on the closed top or bottom side. -/
theorem vtx_mem_closure_trapSet (hT : IsTrap P q i j y₁ y₂) {k : ℕ} (hk : k < P.n)
    (h : P.vtx k ∈ closure (trapSet P i j y₁ y₂)) :
    k ∈ sideVtxSet P i j y₁ ∨ k ∈ sideVtxSet P i j y₂ :=
  (hT.vtx_mem_closedTrap_iff hk).1 (closure_trapSet_subset P i j y₁ y₂ h)

/-! ### The top and bottom vertices depend only on the region -/

/-- If the trapezoid lies in another trapezoid, its top height is at most the other's. -/
theorem top_le_of_subset (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    {q' : Point} {i' j' : ℕ} {y₁' y₂' : ℝ} (_hT' : IsTrap P q' i' j' y₁' y₂')
    (hsub : trapSet P i j y₁ y₂ ⊆ trapSet P i' j' y₁' y₂') : y₂ ≤ y₂' := by
  by_contra hlt
  rw [not_le] at hlt
  have hq2  := (hsub (hT.q_mem hP hq.1)).2.1
  have hmid := hT.mid_mem_trapSet hP hq (y := (y₂' + y₂) / 2) (by linarith [hT.bot_lt])
    (by linarith)
  have h  := (hsub hmid).2.1
  linarith

/-- If the trapezoid lies in another trapezoid, its bottom height is at least the other's. -/
theorem bot_le_of_subset (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    {q' : Point} {i' j' : ℕ} {y₁' y₂' : ℝ} (_hT' : IsTrap P q' i' j' y₁' y₂')
    (hsub : trapSet P i j y₁ y₂ ⊆ trapSet P i' j' y₁' y₂') : y₁' ≤ y₁ := by
  by_contra hlt
  rw [not_le] at hlt
  have hq1  := (hsub (hT.q_mem hP hq.1)).1
  have hmid := hT.mid_mem_trapSet hP hq (y := (y₁ + y₁') / 2) (by linarith)
    (by linarith [hT.lt_top])
  have h  := (hsub hmid).1
  linarith

/-- If the trapezoid lies in another trapezoid, the other's left side line is to the left at
every height of the range. -/
theorem left_le_of_subset (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    {q' : Point} {i' j' : ℕ} {y₁' y₂' : ℝ} (_hT' : IsTrap P q' i' j' y₁' y₂')
    (hsub : trapSet P i j y₁ y₂ ⊆ trapSet P i' j' y₁' y₂') :
    ∀ y ∈ Icc y₁ y₂, edgeX P i' y ≤ edgeX P i y := by
  have hIoo : Ioo y₁ y₂ ⊆ {y | edgeX P i' y ≤ edgeX P i y} := by
    intro y hy
    by_contra hlt
    rw [mem_ofPred_eq, not_le] at hlt
    have hij := hT.edgeX_lt hP hq hy.1 hy.2
    have hmin1 := min_le_left (edgeX P i' y) (edgeX P j y)
    have hmin2 := min_le_right (edgeX P i' y) (edgeX P j y)
    have hlt2  := lt_min hlt hij
    have hp : (((edgeX P i y + min (edgeX P i' y) (edgeX P j y)) / 2, y) : Point) ∈
        trapSet P i j y₁ y₂ :=
      ⟨hy.1, hy.2,
        by show edgeX P i y < (edgeX P i y + min (edgeX P i' y) (edgeX P j y)) / 2; linarith,
        by show (edgeX P i y + min (edgeX P i' y) (edgeX P j y)) / 2 < edgeX P j y; linarith⟩
    have h2  := (hsub hp).2.2.1
    linarith
  have hcl := (isClosed_le (continuous_edgeX P i') (continuous_edgeX P i)).closure_subset_iff.2
    hIoo
  rw [closure_Ioo (hT.bot_lt.trans hT.lt_top).ne] at hcl
  exact fun y hy => hcl hy

/-- If the trapezoid lies in another trapezoid, the other's right side line is to the right at
every height of the range. -/
theorem right_le_of_subset (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    {q' : Point} {i' j' : ℕ} {y₁' y₂' : ℝ} (_hT' : IsTrap P q' i' j' y₁' y₂')
    (hsub : trapSet P i j y₁ y₂ ⊆ trapSet P i' j' y₁' y₂') :
    ∀ y ∈ Icc y₁ y₂, edgeX P j y ≤ edgeX P j' y := by
  have hIoo : Ioo y₁ y₂ ⊆ {y | edgeX P j y ≤ edgeX P j' y} := by
    intro y hy
    by_contra hlt
    rw [mem_ofPred_eq, not_le] at hlt
    have hij := hT.edgeX_lt hP hq hy.1 hy.2
    have hmax1 := le_max_left (edgeX P i y) (edgeX P j' y)
    have hmax2 := le_max_right (edgeX P i y) (edgeX P j' y)
    have hlt2  := max_lt hij hlt
    have hp : (((max (edgeX P i y) (edgeX P j' y) + edgeX P j y) / 2, y) : Point) ∈
        trapSet P i j y₁ y₂ :=
      ⟨hy.1, hy.2,
        by show edgeX P i y < (max (edgeX P i y) (edgeX P j' y) + edgeX P j y) / 2; linarith,
        by show (max (edgeX P i y) (edgeX P j' y) + edgeX P j y) / 2 < edgeX P j y; linarith⟩
    have h2  := (hsub hp).2.2.2
    linarith
  have hcl := (isClosed_le (continuous_edgeX P j) (continuous_edgeX P j')).closure_subset_iff.2
    hIoo
  rw [closure_Ioo (hT.bot_lt.trans hT.lt_top).ne] at hcl
  exact fun y hy => hcl hy

/-- **The top and bottom vertices depend only on the region.**  Two trapezoid data describing
the same open trapezoid have the same top vertex and the same bottom vertex. -/
theorem topVtx_eq_of_trapSet_eq (hP : P.Simple) (hq : q ∈ freeRegion P)
    (hT : IsTrap P q i j y₁ y₂) {q' : Point} {i' j' : ℕ} {y₁' y₂' : ℝ} (hq' : q' ∈ freeRegion P)
    (hT' : IsTrap P q' i' j' y₁' y₂') (h : trapSet P i j y₁ y₂ = trapSet P i' j' y₁' y₂') :
    topVtx P i j y₂ = topVtx P i' j' y₂' ∧ botVtx P i j y₁ = botVtx P i' j' y₁' := by
  have hsub  := h.subset
  have hsub'  := h.symm.subset
  have hy2  := le_antisymm (hT.top_le_of_subset hP hq hT' hsub) (hT'.top_le_of_subset hP hq' hT hsub')
  have hy1  := le_antisymm (hT'.bot_le_of_subset hP hq' hT hsub') (hT.bot_le_of_subset hP hq hT' hsub)
  have h12 := (hT.bot_lt.trans hT.lt_top).le
  have h12' := (hT'.bot_lt.trans hT'.lt_top).le
  have hI2 : y₂ ∈ Icc y₁ y₂ := ⟨h12, le_rfl⟩
  have hI2' : y₂ ∈ Icc y₁' y₂' := by rw [hy2]; exact ⟨h12', le_rfl⟩
  have hI1 : y₁ ∈ Icc y₁ y₂ := ⟨le_rfl, h12⟩
  have hI1' : y₁ ∈ Icc y₁' y₂' := by rw [hy1]; exact ⟨le_rfl, h12'⟩
  have hi2  := le_antisymm (hT'.left_le_of_subset hP hq' hT hsub' y₂ hI2')
      (hT.left_le_of_subset hP hq hT' hsub y₂ hI2)
  have hj2  := le_antisymm (hT.right_le_of_subset hP hq hT' hsub y₂ hI2)
      (hT'.right_le_of_subset hP hq' hT hsub' y₂ hI2')
  have hi1  := le_antisymm (hT'.left_le_of_subset hP hq' hT hsub' y₁ hI1')
      (hT.left_le_of_subset hP hq hT' hsub y₁ hI1)
  have hj1  := le_antisymm (hT.right_le_of_subset hP hq hT' hsub y₁ hI1)
      (hT'.right_le_of_subset hP hq' hT hsub' y₁ hI1')
  have hS2 : sideVtxSet P i j y₂ = sideVtxSet P i' j' y₂' := by
    rw [← hy2]
    ext k
    simp only [sideVtxSet, mem_ofPred_eq]
    rw [hi2, hj2]
  have hS1 : sideVtxSet P i j y₁ = sideVtxSet P i' j' y₁' := by
    rw [← hy1]
    ext k
    simp only [sideVtxSet, mem_ofPred_eq]
    rw [hi1, hj1]
  exact ⟨by unfold topVtx; rw [hS2], by unfold botVtx; rw [hS1]⟩

end

end Chazelle.Visibility.IsTrap
