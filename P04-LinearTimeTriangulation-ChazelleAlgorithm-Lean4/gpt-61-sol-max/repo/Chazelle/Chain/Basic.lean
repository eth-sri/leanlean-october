module

public meta import Chazelle.Arithmetic

public import Chazelle.Visibility.Chord
public import Chazelle.Existence.Arc

/-!
# Subchains of a simple polygon and their box domain

This file sets up the *subchain visibility model* of Chazelle §2 (see
`docs/design-subchain-model.md`).

## The chain

A `Chain` is a simple polygon `P` together with a start index `s` and a number of edges `m`
with `1 ≤ m ≤ n - 1`: the chain consists of the edges `s, s+1, …, s+m-1` of `P` (indices mod
`n`), i.e. of the vertices `s, …, s+m`.  Its point set is `Chain.set`; it is closed, bounded,
contained in `P.boundary`, and misses at least one edge of `P` (`missingIdx`).

* `compl_connected`: **the complement of a simple open chain is connected**.  Proof: the
  complement contains the interior and the exterior of `P`, both connected (Jordan), and
  the midpoint `q` of a missing edge lies in the closure of both; so `Int ∪ {q} ∪ Ext` is
  connected, and `C.setᶜ` lies between it and its closure (every boundary point of `P` is a
  limit of interior points).
* `compl_unbounded`: the complement is unbounded.

## The box domain with a slit

The model works inside the open square `box C.radius` of half-side `radius = coordBound P + 1`,
which contains the chain.  To make the domain simply connected we remove, besides the chain,
a vertical *slit* from a topmost vertex `top` of the chain up to the top side of the box.  No
horizontal chord ever crosses the slit (all chain points are at height `≤ top.2`, and the only
slit point at that height is `top ∈ C`), so the slit is invisible to the visibility map; it
only turns the annulus `box \ C` into a disk `dom = box \ (C ∪ slit)`, so that *every* chord
separates (`Chazelle.Chain.Separation`).

* `box_sdiff_set_connected`: `box r \ C.set` is connected for `r > coordBound P` (clamp the
  connected set `C.setᶜ` into the box).
* `dom_connected`: `dom` is connected (the four corridors of the box around the chain lie in one
  piece of any separation of `dom`, and the slit is a limit of the corridor above the chain).
-/

namespace Chazelle

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Geometry (lerp)

/-- A subchain of a polygon `P`: the `m` consecutive edges `s, s+1, …, s+m-1` (indices modulo
`P.n`), with `1 ≤ m ≤ P.n - 1` so that at least one edge of `P` is missing. -/
structure Chain where
  /-- The ambient polygon. -/
  P : Polygon
  /-- The index of the first edge of the chain. -/
  s : ℕ
  /-- The number of edges of the chain. -/
  m : ℕ
  /-- At least one edge. -/
  one_le : 1 ≤ m
  /-- At least one edge of `P` is missing. -/
  add_one_le : m + 1 ≤ P.n

namespace Chain

variable (C : Chain)

theorem n_pos : 0 < C.P.n := by have := C.add_one_le; omega

theorem m_lt : C.m < C.P.n := by have := C.add_one_le; omega

section
variable (k : ℕ)
include k
/-- The index in `P` of the `k`-th edge of the chain. -/
def edgeIdx : ℕ := (C.s + k) % C.P.n

theorem edgeIdx_lt : C.edgeIdx k < C.P.n := Nat.mod_lt _ C.n_pos

theorem edgeIdx_succ : (C.edgeIdx k + 1) % C.P.n = C.edgeIdx (k + 1) :=
  Existence.mod_add_one_mod _ _ _

/-- The `k`-th vertex of the chain (`k = 0, …, m`). -/
def vertex : Point := C.P.vtx (C.edgeIdx k)

/-- The `k`-th edge of the chain (`k = 0, …, m - 1`), as a set. -/
def chainEdge : Set Point := C.P.edge (C.edgeIdx k)

theorem chainEdge_eq :
    C.chainEdge k = Chazelle.segment (C.vertex k) (C.vertex (k + 1)) := by
  unfold chainEdge Polygon.edge vertex
  rw [edgeIdx_succ]


end

/-- The point set of the chain: the union of its edges. -/
def set : Set Point := {p | ∃ k, k < C.m ∧ p ∈ C.chainEdge k}


theorem chainEdge_subset_boundary (k : ℕ) : C.chainEdge k ⊆ C.P.boundary :=
  Existence.edge_subset_boundary C.P (C.edgeIdx_lt k)

/-- The chain lies on the boundary of `P`. -/
theorem set_subset_boundary : C.set ⊆ C.P.boundary := by
  rintro p ⟨k, -, hp⟩
  exact C.chainEdge_subset_boundary k hp

theorem set_eq_biUnion : C.set = ⋃ k ∈ Finset.range C.m, C.chainEdge k := by
  ext p
  aesop

/-- The chain is a closed set. -/
theorem isClosed_set : IsClosed C.set := by
  rw [set_eq_biUnion]
  exact isClosed_biUnion_finset fun k _ => isClosed_edge C.P _


theorem vertex_mem_chainEdge (k : ℕ) : C.vertex k ∈ C.chainEdge k := by
  rw [chainEdge_eq]; exact Geometry.left_mem_segment _ _

theorem vertex_succ_mem_chainEdge (k : ℕ) : C.vertex (k + 1) ∈ C.chainEdge k := by
  rw [chainEdge_eq]; exact Geometry.right_mem_segment _ _

/-- Every vertex of the chain lies on the chain. -/
theorem vertex_mem_set {k : ℕ} (hk : k ≤ C.m) : C.vertex k ∈ C.set := by
  rcases Nat.lt_or_ge k C.m with h | h
  · exact ⟨k, h, C.vertex_mem_chainEdge k⟩
  · have hkm : k = C.m := le_antisymm hk h
    subst hkm
    refine ⟨C.m - 1, by have := C.one_le; omega, ?_⟩
    have := C.vertex_succ_mem_chainEdge (C.m - 1)
    rwa [Nat.sub_add_cancel C.one_le] at this

/-- Coordinates of chain points are bounded by `coordBound P`. -/
theorem abs_le_coordBound_of_mem_set {p : Point} (hp : p ∈ C.set) :
    |p.1| ≤ coordBound C.P ∧ |p.2| ≤ coordBound C.P :=
  abs_le_coordBound_of_mem_boundary C.P (C.set_subset_boundary hp)

theorem coordBound_nonneg : 0 ≤ coordBound C.P :=
  Finset.sum_nonneg fun _ _ => by positivity

/-! ### The missing edge -/

/-- The index of the edge of `P` following the chain; it is not an edge of the chain. -/
def missingIdx : ℕ := C.edgeIdx C.m

theorem missingIdx_lt : C.missingIdx < C.P.n := C.edgeIdx_lt _

/-- No chain edge is the missing edge. -/
theorem edgeIdx_ne_missingIdx {k : ℕ} (hk : k < C.m) : C.edgeIdx k ≠ C.missingIdx := by
  intro h
  unfold missingIdx edgeIdx at h
  have h1 : C.s + k ≡ C.s + C.m [MOD C.P.n] := h
  have h2 : k ≡ C.m [MOD C.P.n] := Nat.ModEq.add_left_cancel' C.s h1
  have := Nat.ModEq.eq_of_lt_of_lt h2 (by have := C.m_lt; omega) C.m_lt
  omega

/-- The relative interior of the missing edge is off the chain. -/
theorem missing_open_not_mem_set (hP : C.P.Simple) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    lerp (C.P.vtx C.missingIdx) (C.P.vtx ((C.missingIdx + 1) % C.P.n)) t ∉ C.set := by
  rintro ⟨k, hk, hmem⟩
  exact simple_openEdge_not_mem_other hP C.missingIdx_lt ht (C.edgeIdx_lt k)
    (C.edgeIdx_ne_missingIdx hk) hmem

/-- The midpoint of the missing edge. -/
noncomputable def missingMid : Point :=
  lerp (C.P.vtx C.missingIdx) (C.P.vtx ((C.missingIdx + 1) % C.P.n)) (1 / 2)

theorem missingMid_mem_boundary : C.missingMid ∈ C.P.boundary :=
  ⟨C.missingIdx, C.missingIdx_lt, Geometry.lerp_mem_segment _ _ (by norm_num) (by norm_num)⟩

theorem missingMid_not_mem_set (hP : C.P.Simple) : C.missingMid ∉ C.set :=
  C.missing_open_not_mem_set hP ⟨by norm_num, by norm_num⟩

/-! ### Connectedness of the complement -/

/-- **The complement of a simple open chain is connected.** -/
theorem compl_connected (hP : C.P.Simple) : IsPreconnected C.setᶜ := by
  set q := C.missingMid with hq
  have hqb : q ∈ C.P.boundary := C.missingMid_mem_boundary
  have hqC : q ∉ C.set := C.missingMid_not_mem_set hP
  set I := C.P.filled \ C.P.boundary with hI
  set E := C.P.filledᶜ with hE
  have hIq : IsPreconnected (I ∪ {q}) :=
    (filled_sdiff_boundary_connected hP).subset_closure subset_union_left
      (union_subset subset_closure
        (singleton_subset_iff.2 (boundary_subset_closure_interior hP hqb)))
  have hEq : IsPreconnected (E ∪ {q}) :=
    (filled_compl_connected hP).subset_closure subset_union_left
      (union_subset subset_closure (singleton_subset_iff.2 (boundary_subset_closure_compl hP hqb)))
  have hU : IsPreconnected (I ∪ {q} ∪ (E ∪ {q})) :=
    hIq.union q (by simp) (by simp) hEq
  refine hU.subset_closure ?_ ?_
  · rintro p ((hp | hp) | (hp | hp))
    · exact fun h => hp.2 (C.set_subset_boundary h)
    · simp_all
    · exact fun h => hp (boundary_subset_filled _ (C.set_subset_boundary h))
    simp_all
  · intro p hp
    by_cases hb : p ∈ C.P.boundary
    · exact closure_mono (subset_union_left.trans subset_union_left)
        (boundary_subset_closure_interior hP hb)
    · by_cases hf : p ∈ C.P.filled
      · exact subset_closure (Or.inl (Or.inl ⟨hf, hb⟩))
      · exact subset_closure (Or.inr (Or.inl hf))

/-! ### The topmost vertex -/

theorem exists_top : ∃ k, k ≤ C.m ∧ ∀ j, j ≤ C.m → (C.vertex j).2 ≤ (C.vertex k).2 := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range (C.m + 1))
    (fun k => (C.vertex k).2) ⟨0, by simp⟩
  refine ⟨k, by simp_all, fun j hj => hmax j ?_⟩
  simp [hj]

/-- The index of a topmost vertex of the chain: the **least** such index (`Nat.find`), so that it
is determined by the vertex sequence and computable by a left-to-right scan (review finding F7,
`Core.TopIdxSpec`). -/
noncomputable def topIdx : ℕ := by
  classical
  exact Nat.find C.exists_top

theorem topIdx_spec : C.topIdx ≤ C.m ∧ ∀ j, j ≤ C.m → (C.vertex j).2 ≤ (C.vertex C.topIdx).2 := by
  grind [topIdx]

theorem topIdx_le : C.topIdx ≤ C.m := C.topIdx_spec.1

/-- `topIdx` is the least index of a topmost vertex. -/
theorem topIdx_min {j : ℕ} (hj : j ≤ C.m) (htop : ∀ i, i ≤ C.m → (C.vertex i).2 ≤ (C.vertex j).2) :
    C.topIdx ≤ j := by
  classical
  unfold topIdx
  convert Nat.find_min' C.exists_top ⟨hj, htop⟩

/-- A topmost vertex of the chain. -/
noncomputable def top : Point := C.vertex C.topIdx

theorem vertex_snd_le_top {j : ℕ} (hj : j ≤ C.m) : (C.vertex j).2 ≤ C.top.2 :=
  C.topIdx_spec.2 j hj

theorem top_mem_set : C.top ∈ C.set := C.vertex_mem_set C.topIdx_le

/-- Every point of the chain is at height at most `top.2`. -/
theorem snd_le_top_of_mem_set {p : Point} (hp : p ∈ C.set) : p.2 ≤ C.top.2 := by
  obtain ⟨k, hk, hp⟩ := hp
  rw [chainEdge_eq] at hp
  obtain ⟨s, hs0, hs1, rfl⟩ := hp
  have h1 := C.vertex_snd_le_top (j := k) (by omega)
  have h2 := C.vertex_snd_le_top (j := k + 1) (by omega)
  nlinarith

/-! ### The box -/

/-- The open square of half-side `r` centred at the origin. -/
def box (r : ℝ) : Set Point := {p | |p.1| < r ∧ |p.2| < r}

theorem mem_box_iff {r : ℝ} {p : Point} : p ∈ box r ↔ |p.1| < r ∧ |p.2| < r := Iff.rfl

theorem isOpen_box (r : ℝ) : IsOpen (box r) := by
  have : box r = (fun p : Point => p.1) ⁻¹' Ioo (-r) r ∩ (fun p : Point => p.2) ⁻¹' Ioo (-r) r := by
    grind [box, abs_lt]
  rw [this]
  exact (isOpen_Ioo.preimage continuous_fst).inter (isOpen_Ioo.preimage continuous_snd)

theorem convex_box (r : ℝ) : Convex ℝ (box r) := by
  have : box r = ({x : Point | -r < x.1} ∩ {x | x.1 < r}) ∩ ({x | -r < x.2} ∩ {x | x.2 < r}) := by
    ext p; simp [box, abs_lt]
  rw [this]
  exact ((convex_fst_gt _).inter (convex_fst_lt _)).inter ((convex_snd_gt _).inter (convex_snd_lt _))

/-- Clamp a real number into `[-r, r]`. -/
def clampR (r a : ℝ) : ℝ := max (-r) (min r a)

theorem continuous_clampR (r : ℝ) : Continuous (clampR r) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem abs_clampR_le {r : ℝ} (hr : 0 ≤ r) (a : ℝ) : |clampR r a| ≤ r := by
  aesop (add simp [clampR, abs_le]) (add safe (by omega))

theorem clampR_eq_self {r a : ℝ} (h : |a| ≤ r) : clampR r a = a := by
  unfold clampR
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

theorem abs_clampR_eq {r a : ℝ} (hr : 0 ≤ r) (h : r < |a|) : |clampR r a| = r := by
  core_grind

/-- Clamp a point into the closed square of half-side `r`. -/
def clampPt (r : ℝ) (p : Point) : Point := (clampR r p.1, clampR r p.2)

theorem continuous_clampPt (r : ℝ) : Continuous (clampPt r) :=
  ((continuous_clampR r).comp continuous_fst).prodMk ((continuous_clampR r).comp continuous_snd)

theorem clampPt_eq_self {r : ℝ} {p : Point} (h1 : |p.1| ≤ r) (h2 : |p.2| ≤ r) :
    clampPt r p = p := by
  unfold clampPt
  rw [clampR_eq_self h1, clampR_eq_self h2]

/-- **The box minus the chain is connected**, for any box strictly larger than the coordinate
bound: clamping maps the connected set `C.setᶜ` into `box r \ C.set`. -/
theorem box_sdiff_set_connected (hP : C.P.Simple) {r : ℝ} (hr : coordBound C.P < r) :
    IsPreconnected (box r \ C.set) := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  set B := coordBound C.P with hB
  set r' := (max (max |x.1| |x.2|) (max (max |y.1| |y.2|) B) + r) / 2 with hr'
  have hx1 : |x.1| < r := hx.1.1
  have hx2 : |x.2| < r := hx.1.2
  have hy1 : |y.1| < r := hy.1.1
  have hy2 : |y.2| < r := hy.1.2
  have hmax : max (max |x.1| |x.2|) (max (max |y.1| |y.2|) B) < r :=
    max_lt (max_lt hx1 hx2) (max_lt (max_lt hy1 hy2) hr)
  have hr'r : r' < r := by linarith
  have hBr' : B < r' := by
    grind
  have hx1' : |x.1| ≤ r' := by
    grind
  have hx2' : |x.2| ≤ r' := by
    grind
  have hy1' : |y.1| ≤ r' := by
    grind
  have hy2' : |y.2| ≤ r' := by
    grind
  have hr'0 : 0 ≤ r' := (C.coordBound_nonneg.trans hBr'.le)
  refine ⟨clampPt r' '' C.setᶜ, ?_, ?_, ?_,
    (C.compl_connected hP).image _ (continuous_clampPt r').continuousOn⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨⟨lt_of_le_of_lt (abs_clampR_le hr'0 _) hr'r,
      lt_of_le_of_lt (abs_clampR_le hr'0 _) hr'r⟩, ?_⟩
    intro hmem
    by_cases hin : |p.1| ≤ r' ∧ |p.2| ≤ r'
    · rw [clampPt_eq_self hin.1 hin.2] at hmem
      grind
    · have hcoord := C.abs_le_coordBound_of_mem_set hmem
      simp only [clampPt] at hcoord
      rcases not_and_or.1 hin with h | h
      · rw [abs_clampR_eq hr'0 (not_le.1 h)] at hcoord
        linarith
      · rw [abs_clampR_eq hr'0 (not_le.1 h)] at hcoord
        linarith
  · exact ⟨x, hx.2, clampPt_eq_self hx1' hx2'⟩
  · exact ⟨y, hy.2, clampPt_eq_self hy1' hy2'⟩

/-! ### The radius, the slit and the domain -/

/-- The half-side of the box: one more than the coordinate bound of `P`. -/
noncomputable def radius : ℝ := coordBound C.P + 1

theorem coordBound_lt_radius : coordBound C.P < C.radius := by
  unfold radius; linarith

theorem radius_pos : 0 < C.radius := lt_of_le_of_lt C.coordBound_nonneg C.coordBound_lt_radius

/-- The chain lies inside the box. -/
theorem set_subset_box : C.set ⊆ box C.radius := fun _ hp =>
  ⟨lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hp).1 C.coordBound_lt_radius,
    lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hp).2 C.coordBound_lt_radius⟩

theorem top_mem_box : C.top ∈ box C.radius := C.set_subset_box C.top_mem_set

/-- The top end of the slit, on the top side of the box. -/
noncomputable def slitTop : Point := (C.top.1, C.radius)

/-- The slit: the vertical segment from the topmost vertex to the top side of the box. -/
noncomputable def slit : Set Point := Chazelle.segment C.top C.slitTop

theorem top_snd_lt_radius : C.top.2 < C.radius :=
  lt_of_le_of_lt (abs_le.1 (C.abs_le_coordBound_of_mem_set C.top_mem_set).2).2
    C.coordBound_lt_radius

theorem mem_slit_iff {p : Point} :
    p ∈ C.slit ↔ p.1 = C.top.1 ∧ C.top.2 ≤ p.2 ∧ p.2 ≤ C.radius := by
  have hlt := C.top_snd_lt_radius
  constructor
  · intro hp
    refine ⟨fst_eq_of_mem_segment_vertical (u := C.top) (v := C.slitTop) rfl hp, ?_⟩
    obtain ⟨t, ht0, ht1, rfl⟩ := hp
    simp_all [slitTop] <;> nlinarith
  · rintro ⟨h1, h2, h3⟩
    exact mem_segment_of_vertical rfl h1 h2 h3

/-- The obstacle: the chain together with the slit. -/
noncomputable def obstacle : Set Point := C.set ∪ C.slit

/-- The domain of the model: the open box minus the chain and the slit. -/
noncomputable def dom : Set Point := box C.radius \ C.obstacle

theorem isClosed_obstacle : IsClosed C.obstacle :=
  C.isClosed_set.union (Geometry.isClosed_segment _ _)

theorem isOpen_dom : IsOpen C.dom := (isOpen_box _).sdiff C.isClosed_obstacle

theorem isClosed_dom_compl : IsClosed C.domᶜ := C.isOpen_dom.isClosed_compl

theorem dom_subset_box : C.dom ⊆ box C.radius := fun _ h => h.1

theorem mem_dom_iff {p : Point} : p ∈ C.dom ↔ p ∈ box C.radius ∧ p ∉ C.set ∧ p ∉ C.slit := by
  simp only [dom, obstacle, Set.mem_sdiff, mem_union, not_or]

section
variable {p : Point} (hp : p ∈ C.dom)
include hp
theorem not_mem_set_of_mem_dom : p ∉ C.set :=
  (C.mem_dom_iff.1 hp).2.1

theorem not_mem_slit_of_mem_dom : p ∉ C.slit :=
  (C.mem_dom_iff.1 hp).2.2


end

theorem set_subset_dom_compl : C.set ⊆ C.domᶜ := fun _ hp hd => C.not_mem_set_of_mem_dom hd hp

theorem slit_subset_dom_compl : C.slit ⊆ C.domᶜ := fun _ hp hd => C.not_mem_slit_of_mem_dom hd hp

/-- Points of the box above the coordinate bound are in the domain. -/
theorem mem_dom_of_high {p : Point} (hp : p ∈ box C.radius) (hy : coordBound C.P < p.2)
    (hx : p.1 ≠ C.top.1) : p ∈ C.dom := by
  rw [mem_dom_iff]
  refine ⟨hp, fun h => ?_, fun h => hx (C.mem_slit_iff.1 h).1⟩
  have := (abs_le.1 (C.abs_le_coordBound_of_mem_set h).2).2
  linarith

/-- The domain is nonempty. -/
theorem dom_nonempty : C.dom.Nonempty := by
  refine ⟨((coordBound C.P + C.radius) / 2, (coordBound C.P + C.radius) / 2), ?_⟩
  have hB := C.coordBound_nonneg
  have hBr := C.coordBound_lt_radius
  have htop := (abs_le.1 (C.abs_le_coordBound_of_mem_set C.top_mem_set).1).2
  refine C.mem_dom_of_high ⟨?_, ?_⟩ (by linarith) (by linarith)
  all_goals grind

/-! ### Corridors of the box around the chain -/

/-- The part of the box strictly above the chain. -/
noncomputable def upper : Set Point := box C.radius ∩ {p | C.top.2 < p.2}

theorem isOpen_upper : IsOpen C.upper :=
  (isOpen_box _).inter (isOpen_lt continuous_const continuous_snd)

/-- The left corridor: the part of the box to the left of every chain point. -/
noncomputable def corrL : Set Point := box C.radius ∩ {p | p.1 < -coordBound C.P}

/-- The right corridor. -/
noncomputable def corrR : Set Point := box C.radius ∩ {p | coordBound C.P < p.1}

/-- The bottom corridor. -/
noncomputable def corrB : Set Point := box C.radius ∩ {p | p.2 < -coordBound C.P}

/-- The upper corridor, left of the slit. -/
noncomputable def upperL : Set Point := C.upper ∩ {p | p.1 < C.top.1}

/-- The upper corridor, right of the slit. -/
noncomputable def upperR : Set Point := C.upper ∩ {p | C.top.1 < p.1}

theorem convex_upper : Convex ℝ C.upper := (convex_box _).inter (convex_snd_gt _)
theorem convex_corrL : Convex ℝ C.corrL := (convex_box _).inter (convex_fst_lt _)
theorem convex_corrR : Convex ℝ C.corrR := (convex_box _).inter (convex_fst_gt _)
theorem convex_corrB : Convex ℝ C.corrB := (convex_box _).inter (convex_snd_lt _)
theorem convex_upperL : Convex ℝ C.upperL := C.convex_upper.inter (convex_fst_lt _)
theorem convex_upperR : Convex ℝ C.upperR := C.convex_upper.inter (convex_fst_gt _)

theorem abs_top_fst_le : |C.top.1| ≤ coordBound C.P :=
  (C.abs_le_coordBound_of_mem_set C.top_mem_set).1

theorem abs_top_snd_le : |C.top.2| ≤ coordBound C.P :=
  (C.abs_le_coordBound_of_mem_set C.top_mem_set).2

theorem corrL_subset_dom : C.corrL ⊆ C.dom := by
  rintro p ⟨hp, hx⟩
  simp only [mem_ofPred_eq] at hx
  rw [mem_dom_iff]
  refine ⟨hp, fun h => ?_, fun h => ?_⟩
  · have := (abs_le.1 (C.abs_le_coordBound_of_mem_set h).1).1
    linarith
  · have h1 := (C.mem_slit_iff.1 h).1
    have := (abs_le.1 C.abs_top_fst_le).1
    linarith

theorem corrR_subset_dom : C.corrR ⊆ C.dom := by
  rintro p ⟨hp, hx⟩
  simp only [mem_ofPred_eq] at hx
  rw [mem_dom_iff]
  refine ⟨hp, fun h => ?_, fun h => ?_⟩
  · have := (abs_le.1 (C.abs_le_coordBound_of_mem_set h).1).2
    linarith
  · have h1 := (C.mem_slit_iff.1 h).1
    have := (abs_le.1 C.abs_top_fst_le).2
    linarith

theorem corrB_subset_dom : C.corrB ⊆ C.dom := by
  rintro p ⟨hp, hy⟩
  simp only [mem_ofPred_eq] at hy
  rw [mem_dom_iff]
  refine ⟨hp, fun h => ?_, fun h => ?_⟩
  · have := (abs_le.1 (C.abs_le_coordBound_of_mem_set h).2).1
    linarith
  · have h1 := (C.mem_slit_iff.1 h).2.1
    have := (abs_le.1 C.abs_top_snd_le).1
    linarith

theorem upperL_subset_dom : C.upperL ⊆ C.dom := by
  rintro p ⟨⟨hp, hy⟩, hx⟩
  simp only [mem_ofPred_eq] at hx hy
  rw [mem_dom_iff]
  refine ⟨hp, fun h => ?_, fun h => ?_⟩
  · have := C.snd_le_top_of_mem_set h
    linarith
  · have h1 := (C.mem_slit_iff.1 h).1
    linarith

theorem upperR_subset_dom : C.upperR ⊆ C.dom := by
  rintro p ⟨⟨hp, hy⟩, hx⟩
  simp only [mem_ofPred_eq] at hx hy
  rw [mem_dom_iff]
  refine ⟨hp, fun h => ?_, fun h => ?_⟩
  · have := C.snd_le_top_of_mem_set h
    linarith
  · have h1 := (C.mem_slit_iff.1 h).1
    linarith

/-- The midpoint radius `(B + R)/2`, used to name points of the corridors. -/
noncomputable def midR : ℝ := (coordBound C.P + C.radius) / 2

theorem coordBound_lt_midR : coordBound C.P < C.midR := by
  unfold midR; linarith [C.coordBound_lt_radius]

theorem midR_lt_radius : C.midR < C.radius := by
  unfold midR; linarith [C.coordBound_lt_radius]

theorem midR_pos : 0 < C.midR := lt_of_le_of_lt C.coordBound_nonneg C.coordBound_lt_midR

theorem abs_midR : |C.midR| = C.midR := abs_of_pos C.midR_pos

theorem abs_neg_midR : |-C.midR| = C.midR := by rw [abs_neg, abs_midR]

theorem upperL_inter_corrL : (C.upperL ∩ C.corrL).Nonempty := by
  have h1 := C.midR_lt_radius
  have h2 := C.coordBound_lt_midR
  have h3 := (abs_le.1 C.abs_top_fst_le).1
  have h4 := (abs_le.1 C.abs_top_snd_le).2
  refine ⟨(-C.midR, C.midR), ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩ <;>
    simp only [mem_ofPred_eq, abs_neg_midR, abs_midR] <;> linarith

theorem corrL_inter_corrB : (C.corrL ∩ C.corrB).Nonempty := by
  have h1 := C.midR_lt_radius
  have h2 := C.coordBound_lt_midR
  refine ⟨(-C.midR, -C.midR), ⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩ <;>
    simp only [mem_ofPred_eq, abs_neg_midR] <;> linarith

theorem corrB_inter_corrR : (C.corrB ∩ C.corrR).Nonempty := by
  have h1 := C.midR_lt_radius
  have h2 := C.coordBound_lt_midR
  refine ⟨(C.midR, -C.midR), ⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩ <;>
    simp only [mem_ofPred_eq, abs_neg_midR, abs_midR] <;> linarith

theorem corrR_inter_upperR : (C.corrR ∩ C.upperR).Nonempty := by
  have h1 := C.midR_lt_radius
  have h2 := C.coordBound_lt_midR
  have h3 := (abs_le.1 C.abs_top_fst_le).2
  have h4 := (abs_le.1 C.abs_top_snd_le).2
  refine ⟨(C.midR, C.midR), ⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩ <;>
    simp only [mem_ofPred_eq, abs_midR] <;> linarith

/-- A point of the open slit is a limit of points of the upper-left corridor. -/
theorem slit_mem_closure_upperL {p : Point} (hp : p ∈ box C.radius) (hp1 : p.1 = C.top.1)
    (hp2 : C.top.2 < p.2) : p ∈ closure C.upperL := by
  have hcont : Continuous fun δ : ℝ => ((p.1 - δ, p.2) : Point) := by fun_prop
  have htend : Tendsto (fun δ : ℝ => ((p.1 - δ, p.2) : Point)) (𝓝[>] 0) (𝓝 p) := by
    have := hcont.tendsto 0
    simp only [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto htend ?_
  have hε : 0 < C.radius - |p.1| := by linarith [hp.1]
  filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ
  refine ⟨⟨⟨?_, hp.2⟩, ?_⟩, ?_⟩
  all_goals grind

/-- A convex subset of a set with no separation crossing lies on one side. -/
theorem convex_side {u v D K : Set Point} (hu : IsOpen u) (hv : IsOpen v) (hK : Convex ℝ K)
    (hKD : K ⊆ D) (hcov : D ⊆ u ∪ v) (hempty : D ∩ (u ∩ v) = ∅) : K ⊆ u ∨ K ⊆ v := by
  by_cases hKu : (K ∩ u).Nonempty
  · by_cases hKv : (K ∩ v).Nonempty
    · exfalso
      obtain ⟨p, hpK, hpuv⟩ := hK.isPreconnected u v hu hv (hKD.trans hcov) hKu hKv
      have : p ∈ D ∩ (u ∩ v) := ⟨hKD hpK, hpuv⟩
      simp_all
    · left
      intro p hp
      rcases hcov (hKD hp) with h | h
      · exact h
      · exact absurd ⟨p, hp, h⟩ hKv
  · right
    intro p hp
    rcases hcov (hKD hp) with h | h
    · exact absurd ⟨p, hp, h⟩ hKu
    · exact h

/-- Two convex pieces of `D` that meet lie on the same side of a separation. -/
theorem convex_same_side {u v D K K' : Set Point} (hu : IsOpen u) (hv : IsOpen v)
    (hK' : Convex ℝ K') (hK'D : K' ⊆ D) (hcov : D ⊆ u ∪ v) (hempty : D ∩ (u ∩ v) = ∅)
    (hmeet : (K ∩ K').Nonempty) (hKu : K ⊆ u) (hKD : K ⊆ D) : K' ⊆ u := by
  rcases convex_side hu hv hK' hK'D hcov hempty with h | h
  · exact h
  · exfalso
    obtain ⟨p, hpK, hpK'⟩ := hmeet
    have : p ∈ D ∩ (u ∩ v) := ⟨hKD hpK, hKu hpK, h hpK'⟩
    simp_all

/-- The core of the connectedness argument: if both halves of the upper corridor lie in `u`,
then `u, v` cannot separate the domain. -/
theorem dom_connected_aux (hP : C.P.Simple) {u v : Set Point} (hu : IsOpen u) (hv : IsOpen v)
    (hcov : C.dom ⊆ u ∪ v) (hne : (C.dom ∩ v).Nonempty) (hempty : C.dom ∩ (u ∩ v) = ∅)
    (hL : C.upperL ⊆ u) (hR : C.upperR ⊆ u) : False := by
  have hD0 := C.box_sdiff_set_connected hP C.coordBound_lt_radius
  have hdom0 : C.dom ⊆ box C.radius \ C.set := fun p hp => ⟨hp.1, C.not_mem_set_of_mem_dom hp⟩
  have hcov0 : box C.radius \ C.set ⊆ (u ∪ C.upper) ∪ v := by
    intro q hq
    by_cases hqs : q ∈ C.slit
    · left; right
      obtain ⟨hq1, hq2, -⟩ := C.mem_slit_iff.1 hqs
      refine ⟨hq.1, ?_⟩
      simp only [mem_ofPred_eq]
      rcases hq2.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hq.2
        have : q = C.top := Prod.ext hq1 h.symm
        rw [this]; exact C.top_mem_set
    · rcases hcov (C.mem_dom_iff.2 ⟨hq.1, hq.2, hqs⟩) with h | h
      all_goals simp_all
  have hne0 : ((box C.radius \ C.set) ∩ (u ∪ C.upper)).Nonempty := by
    obtain ⟨q, hq⟩ := C.upperL_inter_corrL
    exact ⟨q, hdom0 (C.upperL_subset_dom hq.1), Or.inl (hL hq.1)⟩
  have hne1 : ((box C.radius \ C.set) ∩ v).Nonempty := by
    obtain ⟨q, hq1, hq2⟩ := hne
    exact ⟨q, hdom0 hq1, hq2⟩
  obtain ⟨p, hp0, hpu, hpv⟩ := hD0 (u ∪ C.upper) v (hu.union C.isOpen_upper) hv hcov0 hne0 hne1
  by_cases hpD : p ∈ C.dom
  · rcases hpu with hpu | hpu
    · have : p ∈ C.dom ∩ (u ∩ v) := ⟨hpD, hpu, hpv⟩
      simp_all
    · -- `p` is in the upper corridor and off the slit: in one of the two halves
      have hslit := C.not_mem_slit_of_mem_dom hpD
      have hy : C.top.2 < p.2 := hpu.2
      have hx : p.1 ≠ C.top.1 := by
        intro hx
        exact hslit (C.mem_slit_iff.2 ⟨hx, hy.le, (abs_le.1 hpu.1.2.le).2⟩)
      have hpu' : p ∈ u := by
        rcases lt_or_gt_of_ne hx with h | h
        · exact hL ⟨hpu, h⟩
        · exact hR ⟨hpu, h⟩
      have : p ∈ C.dom ∩ (u ∩ v) := ⟨hpD, hpu', hpv⟩
      simp_all
  · -- `p` is on the open slit: a nearby point of the upper-left corridor is in `v`
    have hpslit : p ∈ C.slit := by
      by_contra h
      exact hpD (C.mem_dom_iff.2 ⟨hp0.1, hp0.2, h⟩)
    obtain ⟨hp1, hp2, -⟩ := C.mem_slit_iff.1 hpslit
    have hp2' : C.top.2 < p.2 := by
      rcases hp2.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hp0.2
        have : p = C.top := Prod.ext hp1 h.symm
        rw [this]; exact C.top_mem_set
    have hcl := C.slit_mem_closure_upperL hp0.1 hp1 hp2'
    obtain ⟨q, hqv, hqU⟩ := mem_closure_iff.1 hcl v hv hpv
    have : q ∈ C.dom ∩ (u ∩ v) := ⟨C.upperL_subset_dom hqU, hL hqU, hqv⟩
    simp_all

/-- **The domain is connected.** -/
theorem dom_connected (hP : C.P.Simple) : IsPreconnected C.dom := by
  intro u v hu hv hcov hneu hnev
  by_contra hempty'
  have hempty : C.dom ∩ (u ∩ v) = ∅ := not_nonempty_iff_eq_empty.1 hempty'
  -- the chain of corridors lies on one side
  have hchain : ∀ w w' : Set Point, IsOpen w → IsOpen w' → C.dom ⊆ w ∪ w' →
      C.dom ∩ (w ∩ w') = ∅ → C.upperL ⊆ w → C.upperR ⊆ w := by
    intro w w' hw hw' hcov' hempty' hL
    have h1 : C.corrL ⊆ w := convex_same_side hw hw' C.convex_corrL C.corrL_subset_dom hcov'
      hempty' C.upperL_inter_corrL hL C.upperL_subset_dom
    have h2 : C.corrB ⊆ w := convex_same_side hw hw' C.convex_corrB C.corrB_subset_dom hcov'
      hempty' C.corrL_inter_corrB h1 C.corrL_subset_dom
    have h3 : C.corrR ⊆ w := convex_same_side hw hw' C.convex_corrR C.corrR_subset_dom hcov'
      hempty' C.corrB_inter_corrR h2 C.corrB_subset_dom
    exact convex_same_side hw hw' C.convex_upperR C.upperR_subset_dom hcov' hempty'
      C.corrR_inter_upperR h3 C.corrR_subset_dom
  have hempty_symm : C.dom ∩ (v ∩ u) = ∅ := by grind
  have hcov_symm : C.dom ⊆ v ∪ u := by grind
  rcases convex_side hu hv C.convex_upperL C.upperL_subset_dom hcov hempty with hL | hL
  · exact C.dom_connected_aux hP hu hv hcov hnev hempty hL (hchain u v hu hv hcov hempty hL)
  · exact C.dom_connected_aux hP hv hu hcov_symm hneu hempty_symm hL
      (hchain v u hv hu hcov_symm hempty_symm hL)

end Chain

end

end Chazelle
