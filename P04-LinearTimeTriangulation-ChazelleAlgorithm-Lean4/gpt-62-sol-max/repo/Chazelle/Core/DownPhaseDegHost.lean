module

public import Chazelle.Core.DownPhaseDegCount
public import Chazelle.Core.Facts2Chain
public import Chazelle.Core.SpecPhases

/-!
# Degree bound on host curves, part 5: `HostFullDegSpec`

The chain model of a chain `C` of a simple polygon is an instance of `HSegObs.GoodH` with `t` any
bound on the number of vertices of `C.P` at one height (`ChainObs.goodH`); chain edges may now be
horizontal and share heights.  Hence (`HSegObs.deg_leH`) `fullDegLe_host`: the full augmented map
has degree at most `2 (t + 1)`.

For a host polygon `H.poly Q` with `Q` of distinct heights, the vertices at one height number at
most `H.length` (`host_ncard_le`): the points of a run at one height coincide, and a `.pt` item
gives one point.  With `HostOk` (`H.length ≤ 64`): **`hostFullDegSpec : HostFullDegSpec`** with
`D = 130`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (IsHChordIn freeIn regionsIn TouchesIn box)
open Chazelle.Visibility (hseg rayPt)
open Chazelle.Geometry (point_ext)

theorem vtx_mem_vertices {P : Polygon} {i : ℕ} (hi : i < P.n) : P.vtx i ∈ P.vertices := by
  simp only [Polygon.vtx]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

namespace ChainObs

open SegObs HSegObs

theorem ord_le (u w : Point) : (ord u w).1.2 ≤ (ord u w).2.2 := by
  unfold ord
  split_ifs with h
  · exact h.le
  · exact not_lt.1 h

variable {C : Chain}

/-- **The segment obstacles of a chain model are `GoodH`** (simple host; `t` bounds the number of
host vertices at one height). -/
theorem goodH (hP : C.P.Simple) {t : ℕ}
    (ht : ∀ y : ℝ, {p | p ∈ C.P.vertices ∧ p.2 = y}.ncard ≤ t) :
    GoodH C.radius (segs C) t := by
  have hR := C.radius_pos
  have htop := C.top_snd_lt_radius
  refine ⟨segs_finite, ?_, fun _ hs _ hp => segs_inbox hs hp, Or.inr (by simp [sideL]),
    Or.inr (by simp [sideR]), fun _ hs _ hs' hne _ hp hp' => segs_cross hP hs hs' hne hp hp', ?_⟩
  · intro s hs
    rcases hs with ⟨k, hk, rfl⟩ | hs
    · exact ord_le _ _
    · simp only [mem_insert_iff, mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl
      · exact htop.le
      · simp only [sideL]; linarith
      · simp only [sideR]; linarith
  · intro y hy
    have hsub : {v | IsVert (segs C) v ∧ v.2 = y} ⊆ {p | p ∈ C.P.vertices ∧ p.2 = y} := by
      rintro v ⟨hv, hvy⟩
      obtain ⟨j, -, rfl⟩ := vert_eq_vertex hv (by rwa [hvy])
      exact ⟨vtx_mem_vertices (C.edgeIdx_lt j), hvy⟩
    exact (ncard_le_ncard hsub ((List.finite_toSet _).subset fun p hp => hp.1)).trans (ht y)

end ChainObs

/-- **The chain half of `HostFullDegSpec`**: for a chain of a simple polygon with at most `t`
vertices at any height, the full augmented map of the chain model has degree at most
`2 (t + 1)`. -/
theorem fullDegLe_host {C : Chain} (hP : C.P.Simple) {t : ℕ}
    (ht : ∀ y : ℝ, {p | p ∈ C.P.vertices ∧ p.2 = y}.ncard ≤ t) (Q : Polygon) :
    (chainModel C).FullDegLe Q (2 * (t + 1)) := by
  intro F hF U hU
  have hdom := ChainObs.dom_eq (C := C)
  show {c | c ∈ C.chords ∪ F ∧ TouchesIn C.dom c U}.ncard ≤ 2 * (t + 1)
  rw [← hdom]
  refine HSegObs.deg_leH (ChainObs.goodH hP ht) (G := C.chords ∪ F) ?_
    (C.chords_finite.union hF.1) (ChainObs.fullAt subset_union_left) (by rwa [hdom])
  rintro c (hc | hc)
  · obtain ⟨k, σ, -, -, -, rfl, hh⟩ := C.chords_spec hc
    exact ⟨_, _, _, by rwa [hdom], C.chordSet_eq_hseg k σ⟩
  · obtain ⟨y, a, b, hh, -, rfl⟩ := hF.2.1 hc
    exact ⟨y, a, b, by rwa [hdom], rfl⟩

/-! ## Host vertices at one height -/

/-- Two vertices of `Q` (indices reduced modulo `n`) at one height coincide (distinct heights). -/
theorem vtx_mod_eq (Q : Polygon) (hDH : DistinctHeights Q) {i j : ℕ}
    (h : (Q.vtx (i % Q.n)).2 = (Q.vtx (j % Q.n)).2) : Q.vtx (i % Q.n) = Q.vtx (j % Q.n) := by
  rcases Nat.eq_zero_or_pos Q.n with h0 | h0
  · have hnil := List.eq_nil_of_length_eq_zero h0
    simp [Polygon.vtx, hnil]
  · by_contra hne
    exact hDH _ _ (Nat.mod_lt _ h0) (Nat.mod_lt _ h0) (fun e => hne (by rw [e])) h

/-- The points of one host item at one height: at most one. -/
theorem item_ncard_le (Q : Polygon) (hDH : DistinctHeights Q) (it : HostItem) (y : ℝ) :
    {p | p ∈ (it.pts Q.n).map (SymPt.eval Q) ∧ p.2 = y}.ncard ≤ 1 := by
  rw [Set.ncard_le_one ((List.finite_toSet _).subset fun p hp => hp.1)]
  rintro p ⟨hp, hpy⟩ p' ⟨hp', hp'y⟩
  cases it with
  | run a ℓ =>
    simp only [HostItem.pts, List.map_map, List.mem_map, List.mem_range,
      Function.comp_apply] at hp hp'
    obtain ⟨k, -, rfl⟩ := hp
    obtain ⟨k', -, rfl⟩ := hp'
    simp only [SymPt.eval] at hpy hp'y ⊢
    exact vtx_mod_eq Q hDH (hpy.trans hp'y.symm)
  | pt x =>
    simp only [HostItem.pts, List.map_cons, List.map_nil, List.mem_singleton] at hp hp'
    rw [hp, hp']

/-- **A host has at most `H.length` vertices at one height.** -/
theorem host_ncard_le (Q : Polygon) (hDH : DistinctHeights Q) (H : Host) (y : ℝ) :
    {p | p ∈ (Host.poly Q H).vertices ∧ p.2 = y}.ncard ≤ H.length := by
  show {p | p ∈ (Host.pts Q.n H).map (SymPt.eval Q) ∧ p.2 = y}.ncard ≤ H.length
  induction H with
  | nil => simp [Host.pts]
  | cons it H ih =>
    have hsub : {p | p ∈ (Host.pts Q.n (it :: H)).map (SymPt.eval Q) ∧ p.2 = y} ⊆
        {p | p ∈ (it.pts Q.n).map (SymPt.eval Q) ∧ p.2 = y} ∪
          {p | p ∈ (Host.pts Q.n H).map (SymPt.eval Q) ∧ p.2 = y} := by
      rintro p ⟨hp, hpy⟩
      simp only [Host.pts, List.flatMap_cons, List.map_append, List.mem_append] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, hpy⟩
      · exact Or.inr ⟨hp, hpy⟩
    have h1 := item_ncard_le Q hDH it y
    calc _ ≤ _ := ncard_le_ncard hsub
          ((((List.finite_toSet _).subset fun p hp => hp.1)).union
            ((List.finite_toSet _).subset fun p hp => hp.1))
      _ ≤ _ := ncard_union_le _ _
      _ ≤ (it :: H).length := by simp only [List.length_cons]; omega

end

end Chazelle.Core
