module

public meta import Chazelle.Arithmetic

public import Chazelle.Visibility.Trapezoid
public import Chazelle.Existence.Diagonal
public import Chazelle.Mountain.Lex

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

section
variable (P : Polygon) (i j : ℕ) (y : ℝ)
include P i j y
/-- The vertices of `P` at height `y` on the closed horizontal segment between the line of
edge `i` and the line of edge `j`. -/
def sideVtxSet : Set ℕ :=
  {k | k < P.n ∧ (P.vtx k).2 = y ∧ edgeX P i y ≤ (P.vtx k).1 ∧ (P.vtx k).1 ≤ edgeX P j y}

theorem sideVtxSet_finite : (sideVtxSet P i j y).Finite :=
  (Set.finite_lt_nat P.n).subset fun _ hk => hk.1


end

section
variable (P : Polygon) (S : Set ℕ)
include P S
/-- The vertex of smallest abscissa in a set of indices (`0` if the set is empty or infinite). -/
noncomputable def leftmostVtx : ℕ :=
  Classical.epsilon fun k => k ∈ S ∧ ∀ k' ∈ S, (P.vtx k).1 ≤ (P.vtx k').1

/-- The vertex of largest abscissa in a set of indices (`0` if the set is empty or infinite). -/
noncomputable def rightmostVtx : ℕ :=
  Classical.epsilon fun k => k ∈ S ∧ ∀ k' ∈ S, (P.vtx k').1 ≤ (P.vtx k).1


end

section
variable (P : Polygon) {S : Set ℕ} (hfin : S.Finite) (hne : S.Nonempty)
include hfin hne
theorem leftmostVtx_spec :
    leftmostVtx P S ∈ S ∧ ∀ k' ∈ S, (P.vtx (leftmostVtx P S)).1 ≤ (P.vtx k').1 :=
  Classical.epsilon_spec (p := fun k => k ∈ S ∧ ∀ k' ∈ S, (P.vtx k).1 ≤ (P.vtx k').1)
    (by
      obtain ⟨a, ha, h⟩ := Set.exists_min_image S (fun k => (P.vtx k).1) hfin hne
      grind)

theorem rightmostVtx_spec :
    rightmostVtx P S ∈ S ∧ ∀ k' ∈ S, (P.vtx k').1 ≤ (P.vtx (rightmostVtx P S)).1 :=
  Classical.epsilon_spec (p := fun k => k ∈ S ∧ ∀ k' ∈ S, (P.vtx k').1 ≤ (P.vtx k).1)
    (by
      obtain ⟨a, ha, h⟩ := Set.exists_max_image S (fun k => (P.vtx k).1) hfin hne
      grind)


end

section
variable (P : Polygon) (i j : ℕ) (y : ℝ)
include P i j y
/-- **The top vertex** of the trapezoid with side edges `i`, `j` and top height `y`: the
leftmost (= `ylexLT`-minimal) vertex of the closed top side. -/
noncomputable def topVtx : ℕ := leftmostVtx P (sideVtxSet P i j y)

/-- **The bottom vertex** of the trapezoid with side edges `i`, `j` and bottom height `y`: the
rightmost (= `ylexLT`-maximal) vertex of the closed bottom side. -/
noncomputable def botVtx : ℕ := rightmostVtx P (sideVtxSet P i j y)

/-! ### Affine bookkeeping -/


end

/-- The abscissa of the line of edge `i` at the height of a point of the segment `a b`. -/
theorem edgeX_lerp_snd (P : Polygon) (i : ℕ) (a b : Point) (s : ℝ) :
    edgeX P i (lerp a b s).2 = (1 - s) * edgeX P i a.2 + s * edgeX P i b.2 := by
  rw [← edgeX_combo P i (by ring : (1 - s) + s = 1)]
  core_grind

/-- For a valid diagonal `(t, b)` (indices in range, distinct, non-adjacent), the arc length
`L` from `t` to `b` satisfies `2 ≤ L ≤ n - 2` and `(t + L) % n = b`. -/
theorem exists_diag_index {P : Polygon} (hn : 3 ≤ P.n) {t b : ℕ} (ht : t < P.n) (hb : b < P.n)
    (htb : t ≠ b) (h1 : b ≠ (t + 1) % P.n) (h2 : t ≠ (b + 1) % P.n) :
    ∃ L, 2 ≤ L ∧ L + 2 ≤ P.n ∧ (t + L) % P.n = b := by
  rw [succIdx_eq P ht] at h1
  rw [succIdx_eq P hb] at h2
  rcases le_or_gt t b with hle | hlt
  · refine ⟨b - t, ?_, ?_, ?_⟩
    · grind
    · grind
    · rw [Nat.add_sub_cancel' hle]; exact Nat.mod_eq_of_lt hb
  · refine ⟨b + P.n - t, ?_, ?_, ?_⟩
    · grind
    · grind
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

section
variable (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
include hP hq hT
/-- **The top side is not reversed**: `edgeX P i y₂ ≤ edgeX P j y₂`.  (Otherwise the two side
lines would cross at a height in `(q.2, y₂)`; the crossing point lies on both edges, so it is a
common vertex, inside the corridor, contradicting `no_vertex`.) -/
theorem edgeX_le_top :
    edgeX P i y₂ ≤ edgeX P j y₂ := by
  by_contra hlt
  rw [not_le] at hlt
  have hq' := hT.q_mem hP hq.1
  have hcont : ContinuousOn (fun y => edgeX P j y - edgeX P i y) (Icc q.2 y₂) :=
    ((continuous_edgeX P j).sub (continuous_edgeX P i)).continuousOn
  have h0 : (0 : ℝ) ∈ Ioo (edgeX P j y₂ - edgeX P i y₂) (edgeX P j q.2 - edgeX P i q.2) :=
    ⟨by linarith, by linarith [hq'.2.2.1, hq'.2.2.2]⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Ioo' hT.lt_top.le hcont h0
  have hfy' : edgeX P j y - edgeX P i y = 0 := hfy
  have hb := hT.bot_lt
  have hzi : ((edgeX P i y, y) : Point) ∈ P.edge i :=
    hT.mem_edgeL (by grind) (by grind) rfl
  have hzj : ((edgeX P i y, y) : Point) ∈ P.edge j :=
    hT.mem_edgeR (by grind) (by grind)
      (by linarith)
  rcases simple_endpoint_of_mem_two hP hT.hi hT.hj (hT.ne hP hq.1) hzi hzj with hz | hz
  · have h := hT.no_vertex i hT.hi
    grind
  · have h := hT.no_vertex _ (succIdx_lt P hT.hi)
    grind

/-- **The bottom side is not reversed**: `edgeX P i y₁ ≤ edgeX P j y₁`. -/
theorem edgeX_le_bot :
    edgeX P i y₁ ≤ edgeX P j y₁ := by
  by_contra hlt
  rw [not_le] at hlt
  have hq' := hT.q_mem hP hq.1
  have hcont : ContinuousOn (fun y => edgeX P j y - edgeX P i y) (Icc y₁ q.2) :=
    ((continuous_edgeX P j).sub (continuous_edgeX P i)).continuousOn
  have h0 : (0 : ℝ) ∈ Ioo (edgeX P j y₁ - edgeX P i y₁) (edgeX P j q.2 - edgeX P i q.2) :=
    ⟨by linarith, by linarith [hq'.2.2.1, hq'.2.2.2]⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Ioo hT.bot_lt.le hcont h0
  have hfy' : edgeX P j y - edgeX P i y = 0 := hfy
  have ht := hT.lt_top
  have hzi : ((edgeX P i y, y) : Point) ∈ P.edge i :=
    hT.mem_edgeL (by grind) (by grind) rfl
  have hzj : ((edgeX P i y, y) : Point) ∈ P.edge j :=
    hT.mem_edgeR (by grind) (by grind)
      (by linarith)
  rcases simple_endpoint_of_mem_two hP hT.hi hT.hj (hT.ne hP hq.1) hzi hzj with hz | hz
  · have h := hT.no_vertex i hT.hi
    grind
  · have h := hT.no_vertex _ (succIdx_lt P hT.hi)
    grind

section
variable {y : ℝ} (h1 : y₁ < y) (h2 : y < y₂)
include y h1 h2
/-- Strictly between the two heights, the left side line is strictly left of the right one. -/
theorem edgeX_lt : edgeX P i y < edgeX P j y := by
  have hq' := hT.q_mem hP hq.1
  have hqlt : edgeX P i q.2 < edgeX P j q.2 := hq'.2.2.1.trans hq'.2.2.2
  have hb := hT.edgeX_le_bot hP hq
  have ht := hT.edgeX_le_top hP hq
  have h12 := hT.bot_lt
  have h23 := hT.lt_top
  rcases le_or_gt y q.2 with hle | hlt
  · obtain ⟨l, hl0, hl1, hy⟩ : ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ y = (1 - l) * y₁ + l * q.2 := by
      refine ⟨(y - y₁) / (q.2 - y₁), div_pos (by linarith) (by linarith), ?_, ?_⟩
      · rw [div_le_one (by linarith)]; linarith
      grind
    rw [hy, edgeX_combo P i (by ring), edgeX_combo P j (by ring)]
    have e1 := mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 hb)
    have e2 := mul_pos hl0 (sub_pos.2 hqlt)
    linarith
  · obtain ⟨l, hl0, hl1, hy⟩ : ∃ l : ℝ, 0 ≤ l ∧ l < 1 ∧ y = (1 - l) * q.2 + l * y₂ := by
      refine ⟨(y - q.2) / (y₂ - q.2), div_nonneg (by linarith) (by linarith), ?_, ?_⟩
      · rw [div_lt_one (by linarith)]; linarith
      grind
    rw [hy, edgeX_combo P i (by ring), edgeX_combo P j (by ring)]
    have e1 := mul_pos (sub_pos.2 hl1) (sub_pos.2 hqlt)
    have e2 := mul_nonneg hl0 (sub_nonneg.2 ht)
    linarith

/-- The midpoint of the horizontal section at a height strictly between the two heights lies in
the trapezoid. -/
theorem mid_mem_trapSet :
    (((edgeX P i y + edgeX P j y) / 2, y) : Point) ∈ trapSet P i j y₁ y₂ := by
  have := hT.edgeX_lt hP hq h1 h2
  exact ⟨h1, h2, by linarith,
    by linarith⟩

/-! ### The top and bottom vertices -/


end

theorem sideVtxSet_top_nonempty : (sideVtxSet P i j y₂).Nonempty := by
  obtain ⟨k, hk, hky, hkx⟩ := hT.top_vertex
  obtain ⟨h1, h2⟩ := hkx (hT.edgeX_le_top hP hq)
  exact ⟨k, hk, hky, h1, h2⟩

theorem sideVtxSet_bot_nonempty : (sideVtxSet P i j y₁).Nonempty := by
  obtain ⟨k, hk, hky, hkx⟩ := hT.bot_vertex
  obtain ⟨h1, h2⟩ := hkx (hT.edgeX_le_bot hP hq)
  exact ⟨k, hk, hky, h1, h2⟩

/-- The top vertex is a vertex of the closed top side, and the leftmost one. -/
theorem topVtx_spec :
    topVtx P i j y₂ ∈ sideVtxSet P i j y₂ ∧
      ∀ k ∈ sideVtxSet P i j y₂, (P.vtx (topVtx P i j y₂)).1 ≤ (P.vtx k).1 :=
  leftmostVtx_spec P (sideVtxSet_finite P i j y₂) (hT.sideVtxSet_top_nonempty hP hq)

/-- The bottom vertex is a vertex of the closed bottom side, and the rightmost one. -/
theorem botVtx_spec :
    botVtx P i j y₁ ∈ sideVtxSet P i j y₁ ∧
      ∀ k ∈ sideVtxSet P i j y₁, (P.vtx k).1 ≤ (P.vtx (botVtx P i j y₁)).1 :=
  rightmostVtx_spec P (sideVtxSet_finite P i j y₁) (hT.sideVtxSet_bot_nonempty hP hq)

theorem topVtx_mem :
    topVtx P i j y₂ ∈ sideVtxSet P i j y₂ := (hT.topVtx_spec hP hq).1

theorem botVtx_mem :
    botVtx P i j y₁ ∈ sideVtxSet P i j y₁ := (hT.botVtx_spec hP hq).1

theorem topVtx_lt :
    topVtx P i j y₂ < P.n := (hT.topVtx_mem hP hq).1

theorem botVtx_lt :
    botVtx P i j y₁ < P.n := (hT.botVtx_mem hP hq).1

/-- The top vertex is at the top height. -/
theorem topVtx_snd :
    (P.vtx (topVtx P i j y₂)).2 = y₂ := (hT.topVtx_mem hP hq).2.1

/-- The bottom vertex is at the bottom height. -/
theorem botVtx_snd :
    (P.vtx (botVtx P i j y₁)).2 = y₁ := (hT.botVtx_mem hP hq).2.1

/-- **The top and bottom vertices are distinct** (their heights differ). -/
theorem topVtx_ne_botVtx :
    topVtx P i j y₂ ≠ botVtx P i j y₁ := by
  intro h
  have h1 := hT.topVtx_snd hP hq
  have h2 := hT.botVtx_snd hP hq
  rw [h] at h1
  linarith [hT.bot_lt, hT.lt_top]

/-- The bottom vertex is strictly below the top vertex. -/
theorem botVtx_snd_lt :
    (P.vtx (botVtx P i j y₁)).2 < (P.vtx (topVtx P i j y₂)).2 := by
  rw [hT.topVtx_snd hP hq, hT.botVtx_snd hP hq]
  exact hT.bot_lt.trans hT.lt_top

/-! ### The segment from the top vertex to the bottom vertex -/

/-- The segment between the top and bottom vertices lies in the closed trapezoid. -/
theorem diag_lerp_mem_closedTrap {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    lerp (P.vtx (topVtx P i j y₂)) (P.vtx (botVtx P i j y₁)) s ∈ closedTrap P i j y₁ y₂ := by
  have hTy := hT.topVtx_snd hP hq
  have hBy := hT.botVtx_snd hP hq
  obtain ⟨-, -, hTi, hTj⟩ := hT.topVtx_mem hP hq
  obtain ⟨-, -, hBi, hBj⟩ := hT.botVtx_mem hP hq
  have h12 := hT.bot_lt.trans hT.lt_top
  refine ⟨?_, ?_, ?_, ?_⟩
  · show y₁ ≤ (lerp _ _ s).2
    rw [lerp_snd, hTy, hBy]; nlinarith
  · show (lerp _ _ s).2 ≤ y₂
    rw [lerp_snd, hTy, hBy]; nlinarith
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


end

section
variable (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) (h1 : botVtx P i j y₁ ≠ (topVtx P i j y₂ + 1) % P.n) (h2 : topVtx P i j y₂ ≠ (botVtx P i j y₁ + 1) % P.n)
include hP hq hT h1 h2
/-- If the top and bottom vertices are not adjacent in `P`, they do not both lie on the line
of the left side edge `i` (else they would be the two endpoints of edge `i`). -/
theorem not_both_on_left :
    ¬ ((P.vtx (topVtx P i j y₂)).1 = edgeX P i y₂ ∧ (P.vtx (botVtx P i j y₁)).1 = edgeX P i y₁) := by
  rintro ⟨hT1, hB1⟩
  have ht := hT.topVtx_lt hP hq
  have hb := hT.botVtx_lt hP hq
  have hTy := hT.topVtx_snd hP hq
  have hBy := hT.botVtx_snd hP hq
  have h12 := (hT.bot_lt.trans hT.lt_top).le
  have hTe : P.vtx (topVtx P i j y₂) ∈ P.edge i :=
    hT.mem_edgeL (by simp_all) (by rw [hTy]) (by simp_all)
  have hBe : P.vtx (botVtx P i j y₁) ∈ P.edge i :=
    hT.mem_edgeL (by rw [hBy]) (by simp_all) (by simp_all)
  have hne := hT.topVtx_ne_botVtx hP hq
  have hsucc := succIdx_lt P hT.hi
  rcases eq_endpoint_of_vtx_mem_edge hP ht hT.hi hTe with e1 | e1 <;>
    rcases eq_endpoint_of_vtx_mem_edge hP hb hT.hi hBe with e2 | e2
  · exact hne ((simple_vtx_inj hP ht hT.hi e1).trans (simple_vtx_inj hP hb hT.hi e2).symm)
  · have f1 := simple_vtx_inj hP ht hT.hi e1
    have f2 := simple_vtx_inj hP hb hsucc e2
    simp_all
  · have f1 := simple_vtx_inj hP ht hsucc e1
    have f2 := simple_vtx_inj hP hb hT.hi e2
    simp_all
  · exact hne ((simple_vtx_inj hP ht hsucc e1).trans (simple_vtx_inj hP hb hsucc e2).symm)

/-- If the top and bottom vertices are not adjacent in `P`, they do not both lie on the line
of the right side edge `j`. -/
theorem not_both_on_right :
    ¬ ((P.vtx (topVtx P i j y₂)).1 = edgeX P j y₂ ∧ (P.vtx (botVtx P i j y₁)).1 = edgeX P j y₁) := by
  rintro ⟨hT1, hB1⟩
  have ht := hT.topVtx_lt hP hq
  have hb := hT.botVtx_lt hP hq
  have hTy := hT.topVtx_snd hP hq
  have hBy := hT.botVtx_snd hP hq
  have h12 := (hT.bot_lt.trans hT.lt_top).le
  have hTe : P.vtx (topVtx P i j y₂) ∈ P.edge j :=
    hT.mem_edgeR (by simp_all) (by rw [hTy]) (by simp_all)
  have hBe : P.vtx (botVtx P i j y₁) ∈ P.edge j :=
    hT.mem_edgeR (by rw [hBy]) (by simp_all) (by simp_all)
  have hne := hT.topVtx_ne_botVtx hP hq
  have hsucc := succIdx_lt P hT.hj
  rcases eq_endpoint_of_vtx_mem_edge hP ht hT.hj hTe with e1 | e1 <;>
    rcases eq_endpoint_of_vtx_mem_edge hP hb hT.hj hBe with e2 | e2
  · exact hne ((simple_vtx_inj hP ht hT.hj e1).trans (simple_vtx_inj hP hb hT.hj e2).symm)
  · have f1 := simple_vtx_inj hP ht hT.hj e1
    have f2 := simple_vtx_inj hP hb hsucc e2
    simp_all
  · have f1 := simple_vtx_inj hP ht hsucc e1
    have f2 := simple_vtx_inj hP hb hT.hj e2
    simp_all
  · exact hne ((simple_vtx_inj hP ht hsucc e1).trans (simple_vtx_inj hP hb hsucc e2).symm)

/-- **The open diagonal lies in the open trapezoid** when the top and bottom vertices are not
adjacent in `P`. -/
theorem diag_lerp_mem_trapSet {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
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
    rw [lerp_snd, hTy, hBy]; nlinarith
  · show (lerp _ _ s).2 < y₂
    rw [lerp_snd, hTy, hBy]; nlinarith
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
theorem diag_segment_cases {p : Point}
    (hp : p ∈ Chazelle.segment (P.vtx (topVtx P i j y₂)) (P.vtx (botVtx P i j y₁))) :
    p = P.vtx (topVtx P i j y₂) ∨ p = P.vtx (botVtx P i j y₁) ∨ p ∈ trapSet P i j y₁ y₂ := by
  obtain ⟨s, hs0, hs1, rfl⟩ := hp
  rcases hs0.lt_or_eq with hs0 | rfl
  · rcases hs1.lt_or_eq with hs1 | rfl
    · exact Or.inr (Or.inr (hT.diag_lerp_mem_trapSet hP hq h1 h2 hs0 hs1))
    simp_all
  simp_all

/-- **The diagonal lemma.**  If the top and bottom vertices of a trapezoid are not adjacent in
`P`, the segment between them is an interior diagonal: `IsDiagonal P s L` with
`s % n = topVtx`, `(s + L) % n = botVtx`, and the closed segment lies in the filled region. -/
theorem exists_isDiagonal :
    ∃ s L, IsDiagonal P s L ∧ s % P.n = topVtx P i j y₂ ∧ (s + L) % P.n = botVtx P i j y₁ ∧
      Chazelle.segment (P.vtx (topVtx P i j y₂)) (P.vtx (botVtx P i j y₁)) ⊆ P.filled := by
  have ht := hT.topVtx_lt hP hq
  have hb := hT.botVtx_lt hP hq
  have hne := hT.topVtx_ne_botVtx hP hq
  obtain ⟨L, hL2, hLn, hsL⟩ := exists_diag_index (simple_three_le hP) ht hb hne h1 h2
  have hs : topVtx P i j y₂ % P.n = topVtx P i j y₂ := Nat.mod_eq_of_lt ht
  refine ⟨topVtx P i j y₂, L, ⟨hL2, hLn, ?_⟩, hs, hsL, ?_⟩
  · rw [hs, hsL]
    intro p hp hpT hpB
    rcases hT.diag_segment_cases hP hq h1 h2 hp with e | e | hin
    · simp_all
    · simp_all
    · exact hT.not_mem_boundary hP hq hin
  · intro p hp
    rcases hT.diag_segment_cases hP hq h1 h2 hp with rfl | rfl | hin
    · exact boundary_subset_filled P (vtx_mem_boundary P ht)
    · exact boundary_subset_filled P (vtx_mem_boundary P hb)
    · exact (hT.trapSet_subset_interior hP hq hin).1

/-! ### The adjacent case: the diagonal is a side edge -/

/-! ### Vertices of the closed trapezoid -/


end

section
variable (hT : IsTrap P q i j y₁ y₂) {k : ℕ} (hk : k < P.n)
include hT hk
/-- **Every vertex of `P` in the closed trapezoid lies on the closed top or bottom side.** -/
theorem vtx_mem_closedTrap_iff :
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
    · exact ⟨hy.ge, by simp_all, by simp_all, by simp_all⟩
    · exact ⟨by simp_all, hy.le, by simp_all, by simp_all⟩

/-- A vertex of `P` in the closure of the trapezoid lies on the closed top or bottom side. -/
theorem vtx_mem_closure_trapSet
    (h : P.vtx k ∈ closure (trapSet P i j y₁ y₂)) :
    k ∈ sideVtxSet P i j y₁ ∨ k ∈ sideVtxSet P i j y₂ :=
  (hT.vtx_mem_closedTrap_iff hk).1 (closure_trapSet_subset P i j y₁ y₂ h)

/-! ### The top and bottom vertices depend only on the region -/


end

section
variable (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) {q' : Point} {i' j' : ℕ} {y₁' y₂' : ℝ} (_hT' : IsTrap P q' i' j' y₁' y₂') (hsub : trapSet P i j y₁ y₂ ⊆ trapSet P i' j' y₁' y₂')
include hP hq hT q' i' j' y₁' y₂' _hT' hsub
/-- If the trapezoid lies in another trapezoid, its top height is at most the other's. -/
theorem top_le_of_subset : y₂ ≤ y₂' := by
  by_contra hlt
  rw [not_le] at hlt
  have hq2 : q.2 < y₂' := (hsub (hT.q_mem hP hq.1)).2.1
  have hmid := hT.mid_mem_trapSet hP hq (y := (y₂' + y₂) / 2) (by linarith [hT.bot_lt])
    (by linarith)
  have h : (y₂' + y₂) / 2 < y₂' := (hsub hmid).2.1
  linarith

/-- If the trapezoid lies in another trapezoid, its bottom height is at least the other's. -/
theorem bot_le_of_subset : y₁' ≤ y₁ := by
  by_contra hlt
  rw [not_le] at hlt
  have hq1 : y₁' < q.2 := (hsub (hT.q_mem hP hq.1)).1
  have hmid := hT.mid_mem_trapSet hP hq (y := (y₁ + y₁') / 2) (by linarith)
    (by linarith [hT.lt_top])
  have h : y₁' < (y₁ + y₁') / 2 := (hsub hmid).1
  linarith

/-- If the trapezoid lies in another trapezoid, the other's left side line is to the left at
every height of the range. -/
theorem left_le_of_subset :
    ∀ y ∈ Icc y₁ y₂, edgeX P i' y ≤ edgeX P i y := by
  have hIoo : Ioo y₁ y₂ ⊆ {y | edgeX P i' y ≤ edgeX P i y} := by
    intro y hy
    by_contra hlt
    rw [mem_ofPred_eq, not_le] at hlt
    have hij := hT.edgeX_lt hP hq hy.1 hy.2
    have hmin1 := min_le_left (edgeX P i' y) (edgeX P j y)
    have hmin2 := min_le_right (edgeX P i' y) (edgeX P j y)
    have hlt2 : edgeX P i y < min (edgeX P i' y) (edgeX P j y) := lt_min hlt hij
    have hp : (((edgeX P i y + min (edgeX P i' y) (edgeX P j y)) / 2, y) : Point) ∈
        trapSet P i j y₁ y₂ :=
      ⟨hy.1, hy.2,
        by linarith,
        by linarith⟩
    have h2 : edgeX P i' y < (edgeX P i y + min (edgeX P i' y) (edgeX P j y)) / 2 :=
      (hsub hp).2.2.1
    linarith
  have hcl := (isClosed_le (continuous_edgeX P i') (continuous_edgeX P i)).closure_subset_iff.2
    hIoo
  rw [closure_Ioo (hT.bot_lt.trans hT.lt_top).ne] at hcl
  grind

/-- If the trapezoid lies in another trapezoid, the other's right side line is to the right at
every height of the range. -/
theorem right_le_of_subset :
    ∀ y ∈ Icc y₁ y₂, edgeX P j y ≤ edgeX P j' y := by
  have hIoo : Ioo y₁ y₂ ⊆ {y | edgeX P j y ≤ edgeX P j' y} := by
    intro y hy
    by_contra hlt
    rw [mem_ofPred_eq, not_le] at hlt
    have hij := hT.edgeX_lt hP hq hy.1 hy.2
    have hmax1 := le_max_left (edgeX P i y) (edgeX P j' y)
    have hmax2 := le_max_right (edgeX P i y) (edgeX P j' y)
    have hlt2 : max (edgeX P i y) (edgeX P j' y) < edgeX P j y := max_lt hij hlt
    have hp : (((max (edgeX P i y) (edgeX P j' y) + edgeX P j y) / 2, y) : Point) ∈
        trapSet P i j y₁ y₂ :=
      ⟨hy.1, hy.2,
        by linarith,
        by linarith⟩
    have h2 : (max (edgeX P i y) (edgeX P j' y) + edgeX P j y) / 2 < edgeX P j' y :=
      (hsub hp).2.2.2
    linarith
  have hcl := (isClosed_le (continuous_edgeX P j) (continuous_edgeX P j')).closure_subset_iff.2
    hIoo
  rw [closure_Ioo (hT.bot_lt.trans hT.lt_top).ne] at hcl
  grind


end

/-- **The top and bottom vertices depend only on the region.**  Two trapezoid data describing
the same open trapezoid have the same top vertex and the same bottom vertex. -/
theorem topVtx_eq_of_trapSet_eq (hP : P.Simple) (hq : q ∈ freeRegion P)
    (hT : IsTrap P q i j y₁ y₂) {q' : Point} {i' j' : ℕ} {y₁' y₂' : ℝ} (hq' : q' ∈ freeRegion P)
    (hT' : IsTrap P q' i' j' y₁' y₂') (h : trapSet P i j y₁ y₂ = trapSet P i' j' y₁' y₂') :
    topVtx P i j y₂ = topVtx P i' j' y₂' ∧ botVtx P i j y₁ = botVtx P i' j' y₁' := by
  have hsub : trapSet P i j y₁ y₂ ⊆ trapSet P i' j' y₁' y₂' := h.subset
  have hsub' : trapSet P i' j' y₁' y₂' ⊆ trapSet P i j y₁ y₂ := h.symm.subset
  have hy2 : y₂ = y₂' :=
    le_antisymm (hT.top_le_of_subset hP hq hT' hsub) (hT'.top_le_of_subset hP hq' hT hsub')
  have hy1 : y₁ = y₁' :=
    le_antisymm (hT'.bot_le_of_subset hP hq' hT hsub') (hT.bot_le_of_subset hP hq hT' hsub)
  have h12 := (hT.bot_lt.trans hT.lt_top).le
  have h12' := (hT'.bot_lt.trans hT'.lt_top).le
  have hI2 : y₂ ∈ Icc y₁ y₂ := ⟨h12, le_rfl⟩
  have hI2' : y₂ ∈ Icc y₁' y₂' := by simp_all
  have hI1 : y₁ ∈ Icc y₁ y₂ := ⟨le_rfl, h12⟩
  have hI1' : y₁ ∈ Icc y₁' y₂' := by simp_all
  have hi2 : edgeX P i y₂ = edgeX P i' y₂ :=
    le_antisymm (hT'.left_le_of_subset hP hq' hT hsub' y₂ hI2')
      (hT.left_le_of_subset hP hq hT' hsub y₂ hI2)
  have hj2 : edgeX P j y₂ = edgeX P j' y₂ :=
    le_antisymm (hT.right_le_of_subset hP hq hT' hsub y₂ hI2)
      (hT'.right_le_of_subset hP hq' hT hsub' y₂ hI2')
  have hi1 : edgeX P i y₁ = edgeX P i' y₁ :=
    le_antisymm (hT'.left_le_of_subset hP hq' hT hsub' y₁ hI1')
      (hT.left_le_of_subset hP hq hT' hsub y₁ hI1)
  have hj1 : edgeX P j y₁ = edgeX P j' y₁ :=
    le_antisymm (hT.right_le_of_subset hP hq hT' hsub y₁ hI1)
      (hT'.right_le_of_subset hP hq' hT hsub' y₁ hI1')
  aesop (add simp [sideVtxSet, mem_ofPred_eq, topVtx, botVtx]) (add safe (by omega))

end

end Chazelle.Visibility.IsTrap
