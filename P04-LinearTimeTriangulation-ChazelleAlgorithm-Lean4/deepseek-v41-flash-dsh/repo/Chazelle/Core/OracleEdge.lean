module

public import Chazelle.Golf

public import Chazelle.Core.OracleQuery

/-!
# Lemma 3.6 (WP-H), part 10: hits on single edges, and the scanned edges as edges of `Q`

The query program tests the edges of the chain one at a time with the sign kernel.  This file
gives the mathematics of one test and of the bookkeeping of the scanned edges.

* `edgeHit`: the answer (`Sweep.FirstHitOpt`) for one non-horizontal edge of `Q` and a ray at the
  height of vertex `h` (`edgeHit_spec`), with its decision by sign tests (`spans_iff`,
  `ahead_iff`, `better_iff`).
* `tci`: the chain edge of a tour position (`tour_seg`), and `wseg`: the points of a walk edge
  that the scan looks at (the chain edge of a tour edge, nothing on the box or the slit);
  `mem_scanSet_iff`: the scanned points of an arc are the union of the `wseg` of its scanned walk
  edges.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideE)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd xAt)

namespace OracleQ

/-! ## One edge -/

section Edge

variable (Q : Polygon)

/-- The height of vertex `h` lies in the (closed) height range of edge `e`. -/
def Spans (e h : ℕ) : Prop :=
  min (Q.vtx e).2 (Q.vtx ((e + 1) % Q.n)).2 ≤ (Q.vtx h).2 ∧
    (Q.vtx h).2 ≤ max (Q.vtx e).2 (Q.vtx ((e + 1) % Q.n)).2

/-- The abscissa of the point of edge `e` at the height of vertex `h`. -/
noncomputable def xe (e h : ℕ) : ℝ := edgeXAt Q e h

open Classical in
/-- **The answer for one edge**: the ray from `z` in direction `σ` at the height of vertex `h`
meets edge `e` at parameter `σ (xe - z.1)` if the height is in range and the parameter is
positive. -/
noncomputable def edgeHit (z : Point) (σ : ℝ) (e h : ℕ) : Option ℝ :=
  if Spans Q e h ∧ 0 < σ * (xe Q e h - z.1) then some (σ * (xe Q e h - z.1)) else none

theorem sigma_sq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ * σ = 1 := by
  rcases hσ with rfl | rfl <;> norm_num

/-- A ray point at the height of the ray lies on a non-horizontal edge iff the height is in range
and the abscissa is the edge's. -/
theorem rayPt_mem_edge_iff {e h : ℕ} (hne : (Q.vtx e).2 ≠ (Q.vtx ((e + 1) % Q.n)).2)
    {z : Point} (hz : z.2 = (Q.vtx h).2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ) :
    rayPt z σ t ∈ Q.edge e ↔ Spans Q e h ∧ t = σ * (xe Q e h - z.1) := by
  unfold Polygon.edge
  Ξ Chazelle.Visibility.mem_segment_iff_xAt hne
  ϴ rayPt_fst, rayPt_snd, hz
  have hx : xAt (Q.vtx e) (Q.vtx ((e + 1) % Q.n)) (Q.vtx h).2 = xe Q e h := rfl
  Ξ hx
  have hs := sigma_sq hσ
  constructor
  · rintro ⟨hsp, hx'⟩
    refine ⟨hsp, ?_⟩
    have : σ * (z.1 + σ * t) = σ * xe Q e h := Ρ hx'
    have e2 : σ * (z.1 + σ * t) = σ * z.1 + (σ * σ) * t := ⋆
    rw [e2, hs] at this
    linarith
  · rintro ⟨hsp, rfl⟩
    refine ⟨hsp, ?_⟩
    have e2 : z.1 + σ * (σ * (xe Q e h - z.1)) = z.1 + (σ * σ) * (xe Q e h - z.1) := ⋆
    rw [e2, hs]; ring

/-- **The answer for one edge.** -/
theorem edgeHit_spec {e h : ℕ} (hne : (Q.vtx e).2 ≠ (Q.vtx ((e + 1) % Q.n)).2)
    {z : Point} (hz : z.2 = (Q.vtx h).2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    Sweep.FirstHitOpt (Q.edge e) z σ (edgeHit Q z σ e h) := by
  unfold edgeHit
  split_ifs with hc
  · refine ⟨hc.2, (rayPt_mem_edge_iff Q hne hz hσ _).2 ⟨hc.1, rfl⟩, fun t' ht' hlt hm => ?_⟩
    have := ((rayPt_mem_edge_iff Q hne hz hσ _).1 hm).2
    linarith
  · intro t ht hm
    obtain ⟨hsp, rfl⟩ := (rayPt_mem_edge_iff Q hne hz hσ _).1 hm
    exact hc ⟨hsp, ht⟩

/-- **The height range by sign tests** (distinct heights, indices in range). -/
theorem spans_iff (hD : DistinctHeights Q) {e h : ℕ} (he : e < Q.n) (hh : h < Q.n) :
    Spans Q e h ↔ (h = e ∨ h = (e + 1) % Q.n) ∨
      ((Q.vtx e).2 < (Q.vtx h).2 ∧ (Q.vtx h).2 < (Q.vtx ((e + 1) % Q.n)).2) ∨
      ((Q.vtx ((e + 1) % Q.n)).2 < (Q.vtx h).2 ∧ (Q.vtx h).2 < (Q.vtx e).2) := by
  have hn : 0 < Q.n := ⋄
  have he1 : (e + 1) % Q.n < Q.n := Nat.mod_lt _ hn
  unfold Spans
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hhe : h = e
    · exact Or.inl (Or.inl hhe)
    by_cases hhe1 : h = (e + 1) % Q.n
    · exact Or.inl (Or.inr hhe1)
    have n1 := hD h e hh he hhe
    have n2 := hD h _ hh he1 hhe1
    right
    rcases le_total (Q.vtx e).2 (Q.vtx ((e + 1) % Q.n)).2 with hle | hle
    · rw [min_eq_left hle] at h1; rw [max_eq_right hle] at h2
      exact Or.inl ⟨lt_of_le_of_ne h1 (Ne.symm n1), lt_of_le_of_ne h2 n2⟩
    · rw [min_eq_right hle] at h1; rw [max_eq_left hle] at h2
      exact Or.inr ⟨lt_of_le_of_ne h1 (Ne.symm n2), lt_of_le_of_ne h2 n1⟩
  · rintro ((rfl | rfl) | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
    · exact ⟨min_le_right _ _, le_max_right _ _⟩
    · exact ⟨(min_le_left _ _).trans h1.le, h2.le.trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans h1.le, h2.le.trans (le_max_left _ _)⟩

/-- **Ahead of the origin, by a sign test.** -/
theorem ahead_iff {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (x z : ℝ) :
    0 < σ * (x - z) ↔ (σ = 1 ∧ z < x) ∨ (σ = -1 ∧ x < z) := by
  rcases hσ with rfl | rfl
  · constructor
    · intro h; left; exact ⟨rfl, ⟡⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith
      · norm_num at h
  · constructor
    · intro h; right; exact ⟨rfl, ⟡⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · norm_num at h
      · linarith

/-- **Comparing two hits, by a sign test.** -/
theorem better_iff {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (x x' z : ℝ) :
    σ * (x - z) < σ * (x' - z) ↔ (σ = 1 ∧ x < x') ∨ (σ = -1 ∧ x' < x) := by
  rcases hσ with rfl | rfl
  · constructor
    · intro h; left; exact ⟨rfl, ⟡⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith
      · norm_num at h
  · constructor
    · intro h; right; exact ⟨rfl, ⟡⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · norm_num at h
      · linarith

end Edge

/-! ## The minimum of two answers -/

/-! ## Tour edges as chain edges -/

section Tour

variable (C : Chain)

/-- **The chain edge of tour position `i`.** -/
noncomputable def tci (i : ℕ) : ℕ := if tj C i < C.m then tj C i else 2 * C.m - 1 - tj C i

theorem tci_lt (i : ℕ) : tci C i < C.m := by
  have := tj_lt C i
  have := C.one_le
  unfold tci; split_ifs <;> omega

/-- **The segment of tour position `i` is the chain edge `tci i`.** -/
theorem tour_seg (i : ℕ) :
    Chazelle.segment (C.sideTour C.sideBeta i) (C.sideTour C.sideBeta (i + 1)) =
      C.chainEdge (tci C i) := by
  rw [C.chainEdge_eq]
  unfold Chain.sideTour
  have e1 : C.sideIdx C.sideBeta i = sideE C.m (tj C i) := Chain.sideIdx_eq C C.sideBeta i
  have e2 : C.sideIdx C.sideBeta (i + 1) = sideE C.m (tj C i + 1) := C.sideIdx_succ C.sideBeta i
  have hj := tj_lt C i
  rw [e1, e2]
  unfold tci
  generalize tj C i = j at hj ⊢
  have sE1 : ∀ x, x ≤ C.m → sideE C.m x = x := fun x hx => by unfold sideE; simp [hx]
  have sE3 : ∀ x, C.m ≤ x → sideE C.m x = 2 * C.m - x := fun x hx => by
    unfold sideE
    rcases eq_or_lt_of_le hx with e | e
    · subst e; simp only [le_refl, ↓reduceIte]; omega
    · simp [show ¬ x ≤ C.m by omega]
  split_ifs with h1
  · rw [sE1 j h1.le, sE1 (j + 1) (by omega)]
  · rw [sE3 j (by omega), sE3 (j + 1) (by omega), Geometry.segment_comm,
      show 2 * C.m - (j + 1) = 2 * C.m - 1 - j by omega,
      show 2 * C.m - j = 2 * C.m - 1 - j + 1 by omega]

/-- **The points of a walk edge that the scan looks at**: the chain edge of a tour edge, nothing
on the box and the slit. -/
noncomputable def wseg (w : ℕ) : Set Point :=
  if 6 ≤ w ∧ w < 2 * C.m + 6 then C.chainEdge (tci C (w - 6)) else ∅

/-- **The scanned points of an arc** are the union of the `wseg` of its scanned walk edges. -/
theorem mem_scanSet_iff (Q : Polygon) (N : NF) (p : ℕ) (x : Point) :
    x ∈ scanSet C Q N p ↔ ∃ k, k ≤ scanLen C Q N p ∧
      x ∈ wseg C (scanIdx (chainModel C).W.n N p k) := by
  constructor
  · rintro ⟨k, hk, i, hi, hidx, hx⟩
    refine ⟨k, hk, ?_⟩
    unfold wseg
    rw [hidx, ite_eq_left (show 6 ≤ i + 6 ∧ i + 6 < 2 * C.m + 6 by omega), show i + 6 - 6 = i by omega, ← tour_seg]
    exact hx
  · rintro ⟨k, hk, hx⟩
    unfold wseg at hx
    split_ifs at hx with hw
    · refine ⟨k, hk, scanIdx (chainModel C).W.n N p k - 6, by omega, by omega, ?_⟩
      rw [tour_seg]; exact hx
    · exact absurd hx (Set.notMem_empty x)

end Tour

end OracleQ

end

end Chazelle.Core
