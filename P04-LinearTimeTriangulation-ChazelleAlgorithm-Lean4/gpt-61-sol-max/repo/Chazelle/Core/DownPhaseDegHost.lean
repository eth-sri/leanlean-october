module

public meta import Chazelle.Arithmetic

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
  grind

namespace ChainObs

open SegObs HSegObs

theorem ord_le (u w : Point) : (ord u w).1.2 ≤ (ord u w).2.2 := by
  grind [ord]

variable {C : Chain}

/-- **The segment obstacles of a chain model are `GoodH`** (simple host; `t` bounds the number of
host vertices at one height). -/
theorem goodH (hP : C.P.Simple) {t : ℕ}
    (ht : ∀ y : ℝ, {p | p ∈ C.P.vertices ∧ p.2 = y}.ncard ≤ t) :
    GoodH C.radius (segs C) t := by
  have hR := C.radius_pos
  have htop := C.top_snd_lt_radius
  have htop2 := (abs_lt.1 C.top_mem_box.2).1
  refine ⟨?_, ?_, ?_, Or.inr (by simp [sideL]), Or.inr (by simp [sideR]), ?_, ?_⟩
  · refine Set.Finite.union (((Set.finite_Iio C.m).image
      fun k => ord (C.vertex k) (C.vertex (k + 1))).subset ?_) (Set.toFinite _)
    rintro s ⟨k, hk, rfl⟩
    grind
  · intro s hs
    rcases hs with ⟨k, hk, rfl⟩ | hs
    · exact ord_le _ _
    · simp only [mem_insert_iff, mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl
      · exact htop.le
      all_goals (grind [sideL, sideR])
  · intro s hs p hp
    rcases seg_cases hs hp with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h, h'⟩ | ⟨-, h, h'⟩
    · have := C.abs_le_coordBound_of_mem_set h
      exact ⟨this.1.trans C.coordBound_lt_radius.le, this.2.trans C.coordBound_lt_radius.le⟩
    · rw [C.mem_slit_iff] at h
      refine ⟨by rw [h.1]; exact abs_top_fst_lt.le, abs_le.2 ⟨by linarith, h.2.2⟩⟩
    all_goals ram_grind
  · intro s hs s' hs' hne p hp hp'
    have hslit : ∀ {p : Point}, p ∈ C.set → p ∈ C.slit → IsVert (segs C) p := by
      intro p h1 h2
      rw [C.mem_slit_iff] at h2
      have hle := C.snd_le_top_of_mem_set h1
      have : p = C.top := point_ext h2.1 (le_antisymm hle h2.2.1)
      exact ⟨slitSeg C, Or.inr (by simp), Or.inl this⟩
    have hsetL : ∀ {p : Point}, p ∈ C.set → p.1 = -C.radius → False := by
      intro p h1 h2
      have := abs_fst_lt_of_set h1
      grind
    have hsetR : ∀ {p : Point}, p ∈ C.set → p.1 = C.radius → False := by
      intro p h1 h2
      have := abs_fst_lt_of_set h1
      grind
    have hslitL : ∀ {p : Point}, p ∈ C.slit → p.1 = -C.radius → False := by
      intro p h1 h2
      rw [C.mem_slit_iff] at h1
      have := abs_top_fst_lt (C := C)
      grind
    have hslitR : ∀ {p : Point}, p ∈ C.slit → p.1 = C.radius → False := by
      intro p h1 h2
      rw [C.mem_slit_iff] at h1
      have := abs_top_fst_lt (C := C)
      grind
    rcases seg_cases hs hp with ⟨h1, k, hk, rfl⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1, -⟩ | ⟨rfl, h1, -⟩ <;>
      rcases seg_cases hs' hp' with ⟨h2, j, hj, rfl⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2, -⟩ | ⟨rfl, h2, -⟩
    · -- two chain edges
      have hkj : k ≠ j := by grind
      have hidx : C.edgeIdx k ≠ C.edgeIdx j := fun h => hkj (C.edgeIdx_inj hk hj h)
      have hmem : p ∈ C.P.edge (C.edgeIdx k) ∩ C.P.edge (C.edgeIdx j) := by
        refine ⟨?_, ?_⟩
        · have := hp; rw [seg_ord, ← C.chainEdge_eq] at this; exact this
        · have := hp'; rw [seg_ord, ← C.chainEdge_eq] at this; exact this
      rw [hP.2.2 _ _ (C.edgeIdx_lt k) (C.edgeIdx_lt j) hidx] at hmem
      obtain ⟨h | h, -⟩ := hmem
      · rw [h]; exact ⟨_, Or.inl ⟨k, hk, rfl⟩, (ord_ends _ _).1⟩
      · rw [h, ← C.vertex_succ_eq]; exact ⟨_, Or.inl ⟨k, hk, rfl⟩, (ord_ends _ _).2⟩
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · linarith
    · grind
    all_goals grind
  · intro y hy
    have hsub : {v | IsVert (segs C) v ∧ v.2 = y} ⊆ {p | p ∈ C.P.vertices ∧ p.2 = y} := by
      rintro v ⟨hv, hvy⟩
      obtain ⟨j, -, rfl⟩ := vert_eq_vertex hv (by simp_all)
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
    (C.chords_finite.union hF.1) (ChainObs.fullAt subset_union_left) (by aesop)
  rintro c (hc | hc)
  · obtain ⟨k, σ, -, -, -, rfl, hh⟩ := C.chords_spec hc
    exact ⟨_, _, _, by ram_grind, C.chordSet_eq_hseg k σ⟩
  · obtain ⟨y, a, b, hh, -, rfl⟩ := hF.2.1 hc
    core_grind

/-! ## Host vertices at one height -/

section
variable (Q : Polygon) (hDH : DistinctHeights Q)
include hDH
/-- Two vertices of `Q` (indices reduced modulo `n`) at one height coincide (distinct heights). -/
theorem vtx_mod_eq {i j : ℕ}
    (h : (Q.vtx (i % Q.n)).2 = (Q.vtx (j % Q.n)).2) : Q.vtx (i % Q.n) = Q.vtx (j % Q.n) := by
  rcases Nat.eq_zero_or_pos Q.n with h0 | h0
  · have hnil : Q.vertices = [] := List.eq_nil_of_length_eq_zero h0
    grind [Polygon.vtx]
  · by_contra hne
    exact hDH _ _ (Nat.mod_lt _ h0) (Nat.mod_lt _ h0) (fun e => hne (by rw [e])) h

/-- The points of one host item at one height: at most one. -/
theorem item_ncard_le (it : HostItem) (y : ℝ) :
    {p | p ∈ (it.pts Q.n).map (SymPt.eval Q) ∧ p.2 = y}.ncard ≤ 1 := by
  rw [Set.ncard_le_one ((List.finite_toSet _).subset fun p hp => hp.1)]
  rintro p ⟨hp, hpy⟩ p' ⟨hp', hp'y⟩
  cases it with
  | run a ℓ =>
    simp only [HostItem.pts, List.map_map, List.mem_map, List.mem_range,
      Function.comp_apply] at hp hp'
    grind [Chazelle.Core.vtx_mod_eq, SymPt.eval]
  | pt x =>
    simp_all [HostItem.pts, List.map_cons, List.map_nil, List.mem_singleton] 

/-- **A host has at most `H.length` vertices at one height.** -/
theorem host_ncard_le (H : Host) (y : ℝ) :
    {p | p ∈ (Host.poly Q H).vertices ∧ p.2 = y}.ncard ≤ H.length := by
  show {p | p ∈ (Host.pts Q.n H).map (SymPt.eval Q) ∧ p.2 = y}.ncard ≤ H.length
  induction H with
  | nil => simp [Host.pts]
  | cons it H ih =>
    have hsub : {p | p ∈ (Host.pts Q.n (it :: H)).map (SymPt.eval Q) ∧ p.2 = y} ⊆
        {p | p ∈ (it.pts Q.n).map (SymPt.eval Q) ∧ p.2 = y} ∪
          {p | p ∈ (Host.pts Q.n H).map (SymPt.eval Q) ∧ p.2 = y} := by
      grind [Host.pts, List.flatMap_cons, List.map_append, List.mem_append]
    have h1 := item_ncard_le Q hDH it y
    calc _ ≤ _ := ncard_le_ncard hsub
          ((((List.finite_toSet _).subset fun p hp => hp.1)).union
            ((List.finite_toSet _).subset fun p hp => hp.1))
      _ ≤ _ := ncard_union_le _ _
      _ ≤ (it :: H).length := by ram_grind


end

end

end Chazelle.Core
