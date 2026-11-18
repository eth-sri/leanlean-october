module

public import Chazelle.Core.Facts2TrapDeg
public import Chazelle.Core.FactsFullDegInt

/-!
# WP-B, part 2: degree `≤ 4` of the full augmented map of a chain model (`FullDegSpec`)

The chain model of a chain `C` (box of half-side `C.radius`, obstacle the chain and the slit) is an
instance of the segment-obstacle setting of `Chazelle.Core.Facts2Trap`: the segments are the chain
edges (ordered by height), the slit and the two vertical sides of the box (`ChainObs.segs`), and
`SegObs.dom C.radius (segs C) = C.dom` (`ChainObs.dom_eq`).  When the host polygon is simple with
pairwise distinct vertex heights:

* the segments satisfy `SegObs.Good` (`ChainObs.good`): chain edges are not horizontal, meet only
  at chain vertices (simplicity), meet the slit only at the top vertex, and the vertices inside the
  box's height range are chain vertices, of distinct heights;
* the vertex chords `C.chords` satisfy `SegObs.FullAt` (`ChainObs.fullAt`): a domain point seen
  horizontally from a chain vertex lies on the chord of that vertex in that direction.

Hence (`SegObs.deg_le_four`) `fullDegLe_chain`: the full augmented map of the chain model has
degree at most `4`, and with the interior half (`fullDeg_interior`) **`fullDegSpec : FullDegSpec`**.

Model dependence: only `C.dom = box \ (chain ∪ slit)`, the vertex chords `C.chords` (through
`FullAt`) and the admissible chords being horizontal chords of the domain are used.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (IsHChordIn freeIn regionsIn TouchesIn box)
open Chazelle.Visibility (hseg rayPt)
open Chazelle.Geometry (point_ext)

namespace ChainObs

open SegObs

/-- A segment given by two points, ordered by height (lower end first). -/
noncomputable def ord (u w : Point) : Point × Point := if u.2 < w.2 then (u, w) else (w, u)

theorem seg_ord (u w : Point) : seg (ord u w) = Chazelle.segment u w := by
  unfold ord seg
  split_ifs
  · rfl
  · exact Geometry.segment_comm _ _

theorem ord_up {u w : Point} (h : u.2 ≠ w.2) : (ord u w).1.2 < (ord u w).2.2 := by
  unfold ord
  split_ifs with h'
  · exact h'
  · exact lt_of_le_of_ne (not_lt.1 h') (Ne.symm h)

theorem ord_ends (u w : Point) :
    (u = (ord u w).1 ∨ u = (ord u w).2) ∧ (w = (ord u w).1 ∨ w = (ord u w).2) := by
  unfold ord
  split_ifs
  · exact ⟨Or.inl rfl, Or.inr rfl⟩
  · exact ⟨Or.inr rfl, Or.inl rfl⟩

theorem ord_cases (u w : Point) {v : Point} (h : v = (ord u w).1 ∨ v = (ord u w).2) :
    v = u ∨ v = w := by
  unfold ord at h
  split_ifs at h
  · exact h
  · exact h.symm

variable (C : Chain)

/-- The left side of the box. -/
noncomputable def sideL : Point × Point := ((-C.radius, -C.radius), (-C.radius, C.radius))

/-- The right side of the box. -/
noncomputable def sideR : Point × Point := ((C.radius, -C.radius), (C.radius, C.radius))

/-- The slit, as a segment. -/
noncomputable def slitSeg : Point × Point := (C.top, C.slitTop)

/-- **The obstacle segments of the chain model**: the chain edges, the slit, the vertical sides
of the box. -/
noncomputable def segs : Set (Point × Point) :=
  {s | ∃ k < C.m, s = ord (C.vertex k) (C.vertex (k + 1))} ∪ {slitSeg C, sideL C, sideR C}

variable {C}

/-- The chain has pairwise distinct vertex indices up to `m`. -/
theorem edgeIdx_inj_le {j k : ℕ} (hj : j ≤ C.m) (hk : k ≤ C.m) (h : C.edgeIdx j = C.edgeIdx k) :
    j = k := by
  unfold Chain.edgeIdx at h
  have h1 : C.s + j ≡ C.s + k [MOD C.P.n] := h
  have h2 : j ≡ k [MOD C.P.n] := Nat.ModEq.add_left_cancel' C.s h1
  exact Nat.ModEq.eq_of_lt_of_lt h2 (by have := C.m_lt; omega) (by have := C.m_lt; omega)

/-- Distinct chain vertices have distinct heights. -/
theorem vertex_snd_ne (hDH : DistinctHeights C.P) {j k : ℕ} (hj : j ≤ C.m) (hk : k ≤ C.m)
    (hjk : j ≠ k) : (C.vertex j).2 ≠ (C.vertex k).2 :=
  hDH _ _ (C.edgeIdx_lt j) (C.edgeIdx_lt k) fun h => hjk (edgeIdx_inj_le hj hk h)

theorem side_seg_fst {R : ℝ} (hR : 0 < R) {x : ℝ} {p : Point}
    (hp : p ∈ seg (((x, -R), (x, R)) : Point × Point)) : p.1 = x ∧ |p.2| ≤ R := by
  obtain ⟨h1, h2, h3⟩ := (mem_seg_iff (s := ((x, -R), (x, R))) (by simp only; linarith)).1 hp
  simp only at h1 h2
  refine ⟨by rw [h3]; simp [xAt], abs_le.2 ⟨h1, h2⟩⟩

/-- Where a point of an obstacle segment lies. -/
theorem seg_cases {s : Point × Point} (hs : s ∈ segs C) {p : Point} (hp : p ∈ seg s) :
    (p ∈ C.set ∧ ∃ k < C.m, s = ord (C.vertex k) (C.vertex (k + 1))) ∨
      (s = slitSeg C ∧ p ∈ C.slit) ∨ (s = sideL C ∧ p.1 = -C.radius ∧ |p.2| ≤ C.radius) ∨
      (s = sideR C ∧ p.1 = C.radius ∧ |p.2| ≤ C.radius) := by
  rcases hs with ⟨k, hk, rfl⟩ | hs
  · left
    refine ⟨⟨k, hk, ?_⟩, k, hk, rfl⟩
    rw [seg_ord] at hp
    rw [C.chainEdge_eq]; exact hp
  · simp only [mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨rfl, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, side_seg_fst C.radius_pos hp⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, side_seg_fst C.radius_pos hp⟩))

theorem abs_fst_lt_of_set {p : Point} (hp : p ∈ C.set) : |p.1| < C.radius :=
  lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hp).1 C.coordBound_lt_radius

theorem abs_top_fst_lt : |C.top.1| < C.radius := C.top_mem_box.1

/-- **The domain of the segment obstacles is the chain domain.** -/
theorem dom_eq : dom C.radius (segs C) = C.dom := by
  ext p
  simp only [dom, Chain.dom, Chain.obstacle, Set.mem_sdiff, Set.mem_union]
  refine and_congr_right fun hbox => not_congr ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨s, hs, hps⟩ := mem_iUnion₂.1 hp
    rcases seg_cases hs hps with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact Or.inl h
    · exact Or.inr h
    · have := hbox.1; rw [h, abs_neg, abs_of_pos C.radius_pos] at this; exact absurd this (lt_irrefl _)
    · have := hbox.1; rw [h, abs_of_pos C.radius_pos] at this; exact absurd this (lt_irrefl _)
  · rcases hp with ⟨k, hk, hpk⟩ | hp
    · refine seg_subset_obs (Or.inl ⟨k, hk, rfl⟩) ?_
      rw [seg_ord, ← C.chainEdge_eq]; exact hpk
    · exact seg_subset_obs (s := slitSeg C) (Or.inr (by simp)) hp

/-- The vertices within the height range of the box are chain vertices. -/
theorem vert_eq_vertex {v : Point} (hv : IsVert (segs C) v) (hvR : |v.2| < C.radius) :
    ∃ j ≤ C.m, v = C.vertex j := by
  obtain ⟨s, hs, hvs⟩ := hv
  rcases hs with ⟨k, hk, rfl⟩ | hs
  · rcases ord_cases _ _ hvs with rfl | rfl
    · exact ⟨k, by omega, rfl⟩
    · exact ⟨k + 1, by omega, rfl⟩
  · simp only [mem_insert_iff, mem_singleton_iff] at hs
    have hR := C.radius_pos
    rcases hs with rfl | rfl | rfl
    · rcases hvs with rfl | rfl
      · exact ⟨C.topIdx, C.topIdx_le, rfl⟩
      · simp [slitSeg, Chain.slitTop, abs_of_pos hR] at hvR
    · rcases hvs with rfl | rfl <;> simp [sideL, abs_of_pos hR] at hvR
    · rcases hvs with rfl | rfl <;> simp [sideR, abs_of_pos hR] at hvR

/-- **The segment obstacles of a chain model are good** (simple host, distinct heights). -/
theorem good (hP : C.P.Simple) (hDH : DistinctHeights C.P) : Good C.radius (segs C) := by
  have hR := C.radius_pos
  have htop := C.top_snd_lt_radius
  have htop2 := (abs_lt.1 C.top_mem_box.2).1
  refine ⟨?_, ?_, ?_, Or.inr (by simp [sideL]), Or.inr (by simp [sideR]), ?_, ?_⟩
  · refine Set.Finite.union (((Set.finite_Iio C.m).image
      fun k => ord (C.vertex k) (C.vertex (k + 1))).subset ?_) (Set.toFinite _)
    rintro s ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · intro s hs
    rcases hs with ⟨k, hk, rfl⟩ | hs
    · exact ord_up (vertex_snd_ne hDH (by omega) (by omega) (by omega))
    · simp only [mem_insert_iff, mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl
      · exact htop
      · simp only [sideL]; linarith
      · simp only [sideR]; linarith
  · intro s hs p hp
    rcases seg_cases hs hp with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h, h'⟩ | ⟨-, h, h'⟩
    · have := C.abs_le_coordBound_of_mem_set h
      exact ⟨this.1.trans C.coordBound_lt_radius.le, this.2.trans C.coordBound_lt_radius.le⟩
    · rw [C.mem_slit_iff] at h
      refine ⟨by rw [h.1]; exact abs_top_fst_lt.le, abs_le.2 ⟨by linarith [h.2.1], h.2.2⟩⟩
    · exact ⟨by rw [h, abs_neg, abs_of_pos hR], h'⟩
    · exact ⟨by rw [h, abs_of_pos hR], h'⟩
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
      rw [h2, abs_neg, abs_of_pos hR] at this; exact lt_irrefl _ this
    have hsetR : ∀ {p : Point}, p ∈ C.set → p.1 = C.radius → False := by
      intro p h1 h2
      have := abs_fst_lt_of_set h1
      rw [h2, abs_of_pos hR] at this; exact lt_irrefl _ this
    have hslitL : ∀ {p : Point}, p ∈ C.slit → p.1 = -C.radius → False := by
      intro p h1 h2
      rw [C.mem_slit_iff] at h1
      have := abs_top_fst_lt (C := C)
      rw [← h1.1, h2, abs_neg, abs_of_pos hR] at this; exact lt_irrefl _ this
    have hslitR : ∀ {p : Point}, p ∈ C.slit → p.1 = C.radius → False := by
      intro p h1 h2
      rw [C.mem_slit_iff] at h1
      have := abs_top_fst_lt (C := C)
      rw [← h1.1, h2, abs_of_pos hR] at this; exact lt_irrefl _ this
    rcases seg_cases hs hp with ⟨h1, k, hk, rfl⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1, -⟩ | ⟨rfl, h1, -⟩ <;>
      rcases seg_cases hs' hp' with ⟨h2, j, hj, rfl⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2, -⟩ | ⟨rfl, h2, -⟩
    · -- two chain edges
      have hkj : k ≠ j := by rintro rfl; exact hne rfl
      have hidx : C.edgeIdx k ≠ C.edgeIdx j := fun h => hkj (C.edgeIdx_inj hk hj h)
      have hmem : p ∈ C.P.edge (C.edgeIdx k) ∩ C.P.edge (C.edgeIdx j) := by
        refine ⟨?_, ?_⟩
        · have := hp; rw [seg_ord, ← C.chainEdge_eq] at this; exact this
        · have := hp'; rw [seg_ord, ← C.chainEdge_eq] at this; exact this
      rw [hP.2.2 _ _ (C.edgeIdx_lt k) (C.edgeIdx_lt j) hidx] at hmem
      obtain ⟨h | h, -⟩ := hmem
      · rw [h]; exact ⟨_, Or.inl ⟨k, hk, rfl⟩, (ord_ends _ _).1⟩
      · rw [h, ← C.vertex_succ_eq]; exact ⟨_, Or.inl ⟨k, hk, rfl⟩, (ord_ends _ _).2⟩
    · exact hslit h1 h2
    · exact (hsetL h1 h2).elim
    · exact (hsetR h1 h2).elim
    · exact hslit h2 h1
    · exact (hne rfl).elim
    · exact (hslitL h1 h2).elim
    · exact (hslitR h1 h2).elim
    · exact (hsetL h2 h1).elim
    · exact (hslitL h2 h1).elim
    · exact (hne rfl).elim
    · rw [h1] at h2; linarith
    · exact (hsetR h2 h1).elim
    · exact (hslitR h2 h1).elim
    · rw [h1] at h2; linarith
    · exact (hne rfl).elim
  · intro v w hv hw hvR hvw
    obtain ⟨j, hj, rfl⟩ := vert_eq_vertex hv hvR
    obtain ⟨k, hk, rfl⟩ := vert_eq_vertex hw (hvw ▸ hvR)
    by_contra hne
    exact vertex_snd_ne hDH hj hk (fun e => hne (by rw [e])) hvw

/-- **The vertex chords of a chain are full** for the segment obstacles: a domain point seen
horizontally from a chain vertex lies on the chord of that vertex in that direction. -/
theorem fullAt {G : Set (Set Point)} (hG : C.chords ⊆ G) : FullAt C.radius (segs C) G := by
  intro v hv hvR z hz hzv hbet
  obtain ⟨j, hj, rfl⟩ := vert_eq_vertex hv hvR
  rw [dom_eq] at hz hbet
  set v := C.vertex j with hvdef
  have hvbox : v ∈ box C.radius := C.set_subset_box (C.vertex_mem_set hj)
  have hzv1 : z.1 ≠ v.1 := fun e => C.not_mem_set_of_mem_dom hz (by
    rw [show z = v from point_ext e hzv]; exact C.vertex_mem_set hj)
  -- the direction and the distance
  obtain ⟨σ, hσ, d, hd, hzd, hint⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ d : ℝ, 0 < d ∧
      z = rayPt v σ d ∧ ∀ t, 0 < t → t < d → rayPt v σ t ∈ C.dom := by
    rcases lt_or_gt_of_ne hzv1 with h | h
    · refine ⟨-1, Or.inr rfl, v.1 - z.1, by linarith, point_ext (by simp) (by simp [hzv]),
        fun t ht1 ht2 => ?_⟩
      have := hbet (v.1 - t) (by rw [min_eq_right h.le]; linarith)
        (by rw [max_eq_left h.le]; linarith)
      simpa [rayPt, sub_eq_add_neg] using this
    · refine ⟨1, Or.inl rfl, z.1 - v.1, by linarith, point_ext (by simp) (by simp [hzv]),
        fun t ht1 ht2 => ?_⟩
      have := hbet (v.1 + t) (by rw [min_eq_left h.le]; linarith)
        (by rw [max_eq_right h.le]; linarith)
      simpa [rayPt] using this
  have hfree : C.DirFree j σ := by
    have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 d := Ioo_mem_nhdsGT hd
    exact e1.mono fun t ht => hint t ht.1 ht.2
  have hle : d ≤ C.chordParam j σ := (C.hit_of_initial hvbox hσ hd hint).1
  have hzc : z ∈ C.chordSet j σ := by
    rw [C.chordSet_eq_image hj hσ hfree]
    exact ⟨d, ⟨hd.le, hle⟩, hzd.symm⟩
  exact ⟨_, hG ⟨j, σ, hj, hσ, hfree, rfl⟩, hzc⟩

end ChainObs

/-- **The chain half of `FullDegSpec`**: for a chain of a simple polygon with pairwise distinct
vertex heights, the full augmented map of the chain model has degree at most `4`. -/
theorem fullDegLe_chain {C : Chain} (hP : C.P.Simple) (hDH : DistinctHeights C.P) (Q : Polygon) :
    (chainModel C).FullDegLe Q 4 := by
  intro F hF U hU
  have hdom := ChainObs.dom_eq (C := C)
  show {c | c ∈ C.chords ∪ F ∧ TouchesIn C.dom c U}.ncard ≤ 4
  rw [← hdom]
  refine SegObs.deg_le_four (ChainObs.good hP hDH) (G := C.chords ∪ F) ?_
    (C.chords_finite.union hF.1) (ChainObs.fullAt subset_union_left) (by rw [hdom]; exact hU)
  rintro c (hc | hc)
  · obtain ⟨k, σ, -, -, -, rfl, hh⟩ := C.chords_spec hc
    exact ⟨_, _, _, by rw [hdom]; exact hh, C.chordSet_eq_hseg k σ⟩
  · obtain ⟨y, a, b, hh, -, rfl⟩ := hF.2.1 hc
    exact ⟨y, a, b, by rw [hdom]; exact hh, rfl⟩

/-- **WP-B: `FullDegSpec`** — the full augmented maps of every chain model of the geometry
polygon and of its interior model have degree at most `4`. -/
theorem fullDegSpec : FullDegSpec := by
  intro P hP hε
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hP
  have hDH : DistinctHeights (Qof P) := (goodShear_epsOf hε).2.1
  refine ⟨fun C hC => ?_, fullDeg_interior P hP hε⟩
  exact fullDegLe_chain (by rw [hC]; exact hQ) (by rw [hC]; exact hDH) (Qof P)

end

end Chazelle.Core
