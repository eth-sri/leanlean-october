module

public meta import Chazelle.Arithmetic

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
  grind

section
variable {e h : ℕ} (hne : (Q.vtx e).2 ≠ (Q.vtx ((e + 1) % Q.n)).2) {z : Point} (hz : z.2 = (Q.vtx h).2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
include hne hz hσ
/-- A ray point at the height of the ray lies on a non-horizontal edge iff the height is in range
and the abscissa is the edge's. -/
theorem rayPt_mem_edge_iff (t : ℝ) :
    rayPt z σ t ∈ Q.edge e ↔ Spans Q e h ∧ t = σ * (xe Q e h - z.1) := by
  unfold Polygon.edge
  rw [Chazelle.Visibility.mem_segment_iff_xAt hne]
  simp only [rayPt_fst, rayPt_snd, hz]
  have hx : xAt (Q.vtx e) (Q.vtx ((e + 1) % Q.n)) (Q.vtx h).2 = xe Q e h := rfl
  rw [hx]
  have hs := sigma_sq hσ
  constructor
  · ram_grind
  ram_grind

/-- **The answer for one edge.** -/
theorem edgeHit_spec :
    Sweep.FirstHitOpt (Q.edge e) z σ (edgeHit Q z σ e h) := by
  unfold edgeHit
  split_ifs with hc
  · refine ⟨hc.2, (rayPt_mem_edge_iff Q hne hz hσ _).2 ⟨hc.1, rfl⟩, fun t' ht' hlt hm => ?_⟩
    have := ((rayPt_mem_edge_iff Q hne hz hσ _).1 hm).2
    linarith
  · intro t ht hm
    obtain ⟨hsp, rfl⟩ := (rayPt_mem_edge_iff Q hne hz hσ _).1 hm
    simp_all


end

/-- **The height range by sign tests** (distinct heights, indices in range). -/
theorem spans_iff (hD : DistinctHeights Q) {e h : ℕ} (he : e < Q.n) (hh : h < Q.n) :
    Spans Q e h ↔ (h = e ∨ h = (e + 1) % Q.n) ∨
      ((Q.vtx e).2 < (Q.vtx h).2 ∧ (Q.vtx h).2 < (Q.vtx ((e + 1) % Q.n)).2) ∨
      ((Q.vtx ((e + 1) % Q.n)).2 < (Q.vtx h).2 ∧ (Q.vtx h).2 < (Q.vtx e).2) := by
  have hn : 0 < Q.n := by omega
  have he1 : (e + 1) % Q.n < Q.n := Nat.mod_lt _ hn
  ram_grind

section
variable {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
include hσ
/-- **Ahead of the origin, by a sign test.** -/
theorem ahead_iff (x z : ℝ) :
    0 < σ * (x - z) ↔ (σ = 1 ∧ z < x) ∨ (σ = -1 ∧ x < z) := by
  rcases hσ with rfl | rfl
  all_goals ram_grind

/-- **Comparing two hits, by a sign test.** -/
theorem better_iff (x x' z : ℝ) :
    σ * (x - z) < σ * (x' - z) ↔ (σ = 1 ∧ x < x') ∨ (σ = -1 ∧ x' < x) := by
  rcases hσ with rfl | rfl
  all_goals ram_grind


end

end Edge

/-! ## The minimum of two answers -/

/-! ## Tour edges as chain edges -/

section Tour

variable (C : Chain)

section
variable (i : ℕ)
include i
/-- **The chain edge of tour position `i`.** -/
noncomputable def tci : ℕ := if tj C i < C.m then tj C i else 2 * C.m - 1 - tj C i

theorem tci_lt : tci C i < C.m := by
  have := tj_lt C i
  grind [tci]

/-- **The segment of tour position `i` is the chain edge `tci i`.** -/
theorem tour_seg :
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
  have sE1 : ∀ x, x ≤ C.m → sideE C.m x = x := fun x hx => by grind [sideE]
  have sE3 : ∀ x, C.m ≤ x → sideE C.m x = 2 * C.m - x := fun x hx => by
    unfold sideE
    grind
  grind [Geometry.segment_comm]


end

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
    grind [wseg, tour_seg]
  · rintro ⟨k, hk, hx⟩
    unfold wseg at hx
    split_ifs at hx with hw
    · refine ⟨k, hk, scanIdx (chainModel C).W.n N p k - 6, by omega, by omega, ?_⟩
      grind [tour_seg]
    simp_all

end Tour

end OracleQ

end

end Chazelle.Core
