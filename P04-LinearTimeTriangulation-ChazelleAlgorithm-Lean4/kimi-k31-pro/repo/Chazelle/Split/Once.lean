module

public import Chazelle.EarClip.SubPoly
public import Chazelle.Existence.SplitDiagonal
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# Splitting a sub-polygon along one interior diagonal

Sub-polygons are given as index lists `l` into a polygon `P` (`Chazelle.EarClip.subPoly P l`,
vertex `k` is `P.vtx l[k]`).  A pair `d = (a, b)` of original indices names the closed segment
`pairSeg P d` from `P.vtx a` to `P.vtx b`.

* `IsDiag P l d`: `d` is an interior diagonal of `subPoly P l`: `a ≠ b` are entries of `l`, the
  segment minus its endpoints avoids the boundary of `subPoly P l`, and the segment lies in its
  filled region.  (Non-adjacency in `l` follows: `isDiagonal_of_isDiag`.)
* `NonCross P d d'`: the two segments meet at most in common endpoints.
* `CycEdge l x y`: `x → y` is a cyclic edge of the list `l`.
* `arcList l s L = (l.rotate s).take (L + 1)`: the entries `l[s], …, l[s + L]` (cyclically);
  `subPoly P (arcList l s L) = (subPoly P l).arc s L` (`subPoly_arcList`).
* `splitFst l d = [a, …, b]` and `splitSnd l d = [b, …, a]` (cyclically along `l`): the two
  pieces of `l` cut along `d`.

## Main results

* `splitPair_split`: for a simple `subPoly P l` and `IsDiag P l d`, the two pieces satisfy the
  symmetric package `SplitPair P l d (splitFst l d) (splitSnd l d)`: both are simple, the filled
  region of `subPoly P l` is the union of theirs, these meet only on the diagonal, the boundaries
  are related as expected, every vertex of `subPoly P l` filled in a piece is a vertex of it, every
  cyclic edge of a piece is an edge of `l` or the diagonal, and the lengths add up to
  `l.length + 2`.  (Transported from `Chazelle.Existence` through `subPoly_arcList`.)
* `SplitPair.isDiag_fst`, `SplitPair.isDiag_snd`: another diagonal `d'` of `subPoly P l` not
  crossing `d` is a diagonal of the first piece when both its endpoints lie in the first piece,
  and of the second piece otherwise (its open segment is connected and lies in the union of the two
  disjoint open interiors); packaged for `splitFst`/`splitSnd` as `isDiag_split_cases`.
* `SplitPair.interior_disjoint`, `SplitPair.interior_not_mem_boundary`,
  `SplitPair.interior_not_mem_chord`, `SplitPair.interior_not_mem_filled`: the interior of a piece
  avoids the other piece, the boundary of `subPoly P l` and the diagonal.
* `weakTriangulates_split`: weak triangulations of the two pieces (in positions of the pieces)
  relabel (`relabel`) to a weak triangulation of `subPoly P l` (in positions of `l`), and
  `relabelList_relabel_fst` / `relabelList_relabel_snd` express this relabelling in original
  indices.
-/

namespace Chazelle.Split

@[expose] public section

open Set Topology
open Chazelle.Jordan (isOpen_filled_sdiff_boundary interior_filled isClosed_filled)
open Chazelle.Existence (IsDiagonal WeakTriangulates relabel)
open Chazelle.EarClip (subPoly n_subPoly vtx_subPoly vtx_subPoly_getD getD_eq_getElem_of_lt
  polygon_ext vertices_subPoly relabelList)
open Chazelle.Geometry (lerp continuous_lerp lerp_mem_segment segment_eq_image_lerp)

/-! ### Segments named by index pairs -/

/-- The closed segment joining the vertices of `P` named by an index pair. -/
def pairSeg (P : Polygon) (d : ℕ × ℕ) : Set Point := Chazelle.segment (P.vtx d.1) (P.vtx d.2)

/-- The segment of the swapped pair is the same set. -/
theorem pairSeg_swap (P : Polygon) (d : ℕ × ℕ) : pairSeg P d.swap = pairSeg P d :=
  Chazelle.Geometry.segment_comm _ _

/-- The open segment `{lerp a b t | 0 < t < 1}`. -/
def innerSeg (a b : Point) : Set Point := lerp a b '' Ioo (0 : ℝ) 1

/-- The open segment lies in the closed segment. -/
theorem innerSeg_subset (a b : Point) : innerSeg a b ⊆ Chazelle.segment a b := by
  rintro _ ⟨t, ht, rfl⟩
  exact lerp_mem_segment a b ht.1.le ht.2.le

/-- A point of the open segment is neither endpoint (for distinct endpoints). -/
theorem ne_of_mem_innerSeg {a b p : Point} (hab : a ≠ b) (hp : p ∈ innerSeg a b) :
    p ≠ a ∧ p ≠ b := by
  obtain ⟨t, ht, rfl⟩ := hp
  exact ⟨Chazelle.Jordan.lerp_ne_left hab ht.1, Chazelle.Jordan.lerp_ne_right hab ht.2⟩

/-- A point of the closed segment other than the endpoints is in the open segment. -/
theorem mem_innerSeg_of_ne {a b p : Point} (hp : p ∈ Chazelle.segment a b) (ha : p ≠ a)
    (hb : p ≠ b) : p ∈ innerSeg a b := by
  obtain ⟨t, h0, h1, rfl⟩ := hp
  refine ⟨t, ⟨lt_of_le_of_ne h0 ?_, lt_of_le_of_ne h1 ?_⟩, rfl⟩
  · rintro rfl
    exact ha (Chazelle.Geometry.lerp_zero a b)
  · rintro rfl
    exact hb (Chazelle.Geometry.lerp_one a b)

/-- The open segment is preconnected. -/
theorem isPreconnected_innerSeg (a b : Point) : IsPreconnected (innerSeg a b) :=
  isPreconnected_Ioo.image _ (continuous_lerp a b).continuousOn

/-- The open segment is nonempty. -/
theorem innerSeg_nonempty (a b : Point) : (innerSeg a b).Nonempty :=
  ⟨lerp a b (1 / 2), 1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩

/-- The closed segment lies in the closure of the open segment. -/
theorem segment_subset_closure_innerSeg (a b : Point) :
    Chazelle.segment a b ⊆ closure (innerSeg a b) := by
  rw [segment_eq_image_lerp, ← closure_Ioo (zero_ne_one' ℝ)]
  exact image_closure_subset_closure_image (continuous_lerp a b)

/-- A segment with distinct endpoints has a point other than its endpoints. -/
theorem exists_inner_point {a b : Point} (hab : a ≠ b) :
    ∃ p ∈ Chazelle.segment a b, p ≠ a ∧ p ≠ b := by
  obtain ⟨p, hp⟩ := innerSeg_nonempty a b
  exact ⟨p, innerSeg_subset a b hp, ne_of_mem_innerSeg hab hp⟩

/-! ### Diagonals of a sub-polygon -/

/-- `d` is an interior diagonal of the sub-polygon `subPoly P l`: its endpoints are distinct
entries of `l`, its segment minus the endpoints avoids the boundary of `subPoly P l`, and its
segment lies in the filled region of `subPoly P l`. -/
def IsDiag (P : Polygon) (l : List ℕ) (d : ℕ × ℕ) : Prop :=
  d.1 ∈ l ∧ d.2 ∈ l ∧ d.1 ≠ d.2 ∧
    (∀ p ∈ pairSeg P d, p ≠ P.vtx d.1 → p ≠ P.vtx d.2 → p ∉ (subPoly P l).boundary) ∧
    pairSeg P d ⊆ (subPoly P l).filled

/-- Two index pairs are *non-crossing*: their segments meet at most in common endpoints. -/
def NonCross (P : Polygon) (d d' : ℕ × ℕ) : Prop :=
  pairSeg P d ∩ pairSeg P d' ⊆ ({P.vtx d.1, P.vtx d.2} : Set Point) ∩ {P.vtx d'.1, P.vtx d'.2}

/-- `x → y` is a cyclic edge of the index list `l`. -/
def CycEdge (l : List ℕ) (x y : ℕ) : Prop :=
  ∃ k < l.length, l.getD k 0 = x ∧ l.getD ((k + 1) % l.length) 0 = y

/-- Each position of `l` gives a cyclic edge. -/
theorem cycEdge_self (l : List ℕ) {k : ℕ} (hk : k < l.length) :
    CycEdge l (l.getD k 0) (l.getD ((k + 1) % l.length) 0) :=
  ⟨k, hk, rfl, rfl⟩

/-! ### Vertices of a simple sub-polygon -/

variable (P : Polygon)

/-- An entry of `l` is a vertex of `subPoly P l`. -/
theorem vtx_mem_boundary_subPoly {l : List ℕ} {x : ℕ} (hx : x ∈ l) :
    P.vtx x ∈ (subPoly P l).boundary := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  rw [← vtx_subPoly P l hi]
  exact Chazelle.Existence.vtx_mem_boundary _ (by rwx [n_subPoly])

/-- In a simple sub-polygon, `P.vtx` is injective on the entries of `l`. -/
theorem eq_of_vtx_eq {l : List ℕ} (hQ : (subPoly P l).Simple) {x y : ℕ} (hx : x ∈ l)
    (hy : y ∈ l) (h : P.vtx x = P.vtx y) : x = y := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
  rw [← vtx_subPoly P l hi, ← vtx_subPoly P l hj] at h
  have := hQ.2.1 i j (by rwx [n_subPoly]) (by rwx [n_subPoly]) h
  subst this
  rfl

/-- A simple sub-polygon has no repeated index. -/
theorem nodup_of_simple {l : List ℕ} (hQ : (subPoly P l).Simple) : l.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j h
  have hi : (i : ℕ) < (subPoly P l).n := by rw [n_subPoly]; exact i.2
  have hj : (j : ℕ) < (subPoly P l).n := by rw [n_subPoly]; exact j.2
  apply Fin.ext
  apply hQ.2.1 i j hi hj
  rw [vtx_subPoly P l i.2, vtx_subPoly P l j.2]
  simp only [List.get_eq_getElem] at h
  rw [h]

/-- A simple sub-polygon has at least three entries. -/
theorem three_le_of_simple {l : List ℕ} (hQ : (subPoly P l).Simple) : 3 ≤ l.length := by
  have := hQ.1
  rwa [n_subPoly] at this

/-- The vertex of `subPoly P l` at the position of an entry `x` is `P.vtx x`. -/
theorem vtx_idxOf {l : List ℕ} {x : ℕ} (hx : x ∈ l) :
    (subPoly P l).vtx (l.idxOf x) = P.vtx x := by
  rw [vtx_subPoly P l (List.idxOf_lt_length_of_mem hx), List.getElem_idxOf]

/-- `getD` at the position of an entry. -/
theorem getD_idxOf {l : List ℕ} {x : ℕ} (hx : x ∈ l) : l.getD (l.idxOf x) 0 = x := by
  rw [getD_eq_getElem_of_lt _ _ (List.idxOf_lt_length_of_mem hx), List.getElem_idxOf]

/-- The endpoints of a diagonal are distinct points. -/
theorem IsDiag.vtx_ne {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ} (hd : IsDiag P l d) :
    P.vtx d.1 ≠ P.vtx d.2 :=
  fun h => hd.2.2.1 (eq_of_vtx_eq P hQ hd.1 hd.2.1 h)

/-! ### Arcs of an index list -/

/-- The entries `l[s], l[s + 1], …, l[s + L]` of `l` (indices modulo `l.length`). -/
def arcList (l : List ℕ) (s L : ℕ) : List ℕ := (l.rotate s).take (L + 1)

/-- An arc of length `L < l.length` has `L + 1` entries. -/
theorem length_arcList {l : List ℕ} {s L : ℕ} (hL : L < l.length) :
    (arcList l s L).length = L + 1 := by
  simp only [arcList, List.length_take, List.length_rotate]
  omega

/-- Entry `k ≤ L` of `arcList l s L` is `l[(s + k) % l.length]`. -/
theorem getD_arcList {l : List ℕ} {s L k : ℕ} (hL : L < l.length) (hk : k ≤ L) :
    (arcList l s L).getD k 0 = l.getD ((s + k) % l.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, arcList,
    List.getElem?_take_of_lt (by omega), List.getElem?_rotate (by omega), Nat.add_comm k s]

/-- Entries of an arc of `l` are entries of `l`. -/
theorem mem_of_mem_arcList {l : List ℕ} {s L x : ℕ} (h : x ∈ arcList l s L) : x ∈ l :=
  List.mem_rotate.1 (List.mem_of_mem_take h)

/-- **The sub-polygon of an arc of `l` is the arc of the sub-polygon.** -/
theorem subPoly_arcList (l : List ℕ) (s : ℕ) {L : ℕ} (hL : L < l.length) :
    subPoly P (arcList l s L) = (subPoly P l).arc s L := by
  apply polygon_ext
  rw [vertices_subPoly]
  unfold Polygon.arc
  apply List.ext_getElem
  · rw [List.length_map, List.length_map, List.length_range, length_arcList hL]
  · intro k h1 h2
    have hk : k < L + 1 := by simpa using h2
    simp only [List.getElem_map, List.getElem_range, n_subPoly]
    rw [← getD_eq_getElem_of_lt _ 0 (by rwx [length_arcList hL]),
      getD_arcList hL (by omega), vtx_subPoly_getD P l (Nat.mod_lt _ (by omega))]

/-- A cyclic edge of an arc of `l` is a cyclic edge of `l`, or the closing edge from `l[s + L]`
back to `l[s]`. -/
theorem arcList_edge {l : List ℕ} {s L : ℕ} (hL : L < l.length) {k : ℕ}
    (hk : k < (arcList l s L).length) :
    CycEdge l ((arcList l s L).getD k 0)
        ((arcList l s L).getD ((k + 1) % (arcList l s L).length) 0) ∨
      ((arcList l s L).getD k 0 = l.getD ((s + L) % l.length) 0 ∧
        (arcList l s L).getD ((k + 1) % (arcList l s L).length) 0 = l.getD (s % l.length) 0) := by
  rw [length_arcList hL] at hk ⊢
  rcases Nat.lt_or_ge k L with hkL | hkL
  · left
    refine ⟨(s + k) % l.length, Nat.mod_lt _ (by omega), (getD_arcList hL hkL.le).symm, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega : k + 1 < L + 1), getD_arcList hL hkL,
      Chazelle.Existence.mod_add_one_mod]
  · right
    have hk' : k = L := by omega
    subst hk'
    rw [Nat.mod_self, getD_arcList hL le_rfl, getD_arcList hL (Nat.zero_le _), Nat.add_zero]
    exact ⟨rfl, rfl⟩

/-! ### The two pieces of a diagonal -/

/-- The length `L` of the arc of `l` from `d.1` to `d.2`: `(idx d.2 - idx d.1) mod l.length`. -/
def diagLen (l : List ℕ) (d : ℕ × ℕ) : ℕ := (l.idxOf d.2 + l.length - l.idxOf d.1) % l.length

/-- The first piece `[d.1, …, d.2]` (cyclically along `l`) of `l` cut along `d`. -/
def splitFst (l : List ℕ) (d : ℕ × ℕ) : List ℕ := arcList l (l.idxOf d.1) (diagLen l d)

/-- The second piece `[d.2, …, d.1]` (cyclically along `l`) of `l` cut along `d`. -/
def splitSnd (l : List ℕ) (d : ℕ × ℕ) : List ℕ :=
  arcList l (l.idxOf d.2) (l.length - diagLen l d)

/-- Position arithmetic for a pair of distinct entries of `l`. -/
theorem diagLen_spec {l : List ℕ} {d : ℕ × ℕ} (h1 : d.1 ∈ l) (h2 : d.2 ∈ l) (hne : d.1 ≠ d.2) :
    1 ≤ diagLen l d ∧ diagLen l d < l.length ∧
      (l.idxOf d.1 + diagLen l d) % l.length = l.idxOf d.2 := by
  have hs := List.idxOf_lt_length_of_mem h1
  have he := List.idxOf_lt_length_of_mem h2
  have hse : l.idxOf d.1 ≠ l.idxOf d.2 := by
    intro h
    have := getD_idxOf h1
    rw [h, getD_idxOf h2] at this
    exact hne this.symm
  have hsL : (l.idxOf d.1 + diagLen l d) % l.length = l.idxOf d.2 := by
    unfold diagLen
    rw [Nat.add_mod_mod, show l.idxOf d.1 + (l.idxOf d.2 + l.length - l.idxOf d.1) =
      l.idxOf d.2 + l.length by omega, Nat.add_mod_right, Nat.mod_eq_of_lt he]
  refine ⟨?_, Nat.mod_lt _ (by omega), hsL⟩
  by_contra h0
  have h0' : diagLen l d = 0 := by omega
  rw [h0', Nat.add_zero, Nat.mod_eq_of_lt hs] at hsL
  exact hse hsL

variable {P}

/-- The segment of a diagonal is not contained in an edge of the sub-polygon. -/
theorem IsDiag.not_subset_edge {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ}
    (hd : IsDiag P l d) {k : ℕ} (hk : k < l.length) (h : pairSeg P d ⊆ (subPoly P l).edge k) :
    False := by
  obtain ⟨p, hp, hp1, hp2⟩ := exists_inner_point (hd.vtx_ne P hQ)
  exact hd.2.2.2.1 p hp hp1 hp2
    (Chazelle.Existence.edge_subset_boundary _ (by rwx [n_subPoly]) (h hp))

/-- **An `IsDiag` pair is a diagonal in the sense of `Chazelle.Existence.IsDiagonal`**, at the
position `s` of its first endpoint with arc length `L` (the positions of the endpoints are given
by `hs`, `he`). -/
theorem isDiagonal_of_isDiag {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ}
    (hd : IsDiag P l d) {s L : ℕ} (hsn : s < l.length) (hs : l.getD s 0 = d.1) (hL1 : 1 ≤ L)
    (hLn : L < l.length) (he : l.getD ((s + L) % l.length) 0 = d.2) :
    IsDiagonal (subPoly P l) s L := by
  have hQn  := n_subPoly P l
  have hv1 : (subPoly P l).vtx s = P.vtx d.1 := by rw [vtx_subPoly_getD P l hsn, hs]
  have hv2 : (subPoly P l).vtx ((s + L) % l.length) = P.vtx d.2 := by
    rw [vtx_subPoly_getD P l (Nat.mod_lt _ (by omega)), he]
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    have hL : L = 1 := by omega
    subst hL
    apply hd.not_subset_edge hQ hsn
    unfold Polygon.edge
    rw [hQn, hv1, hv2]
    exact le_rfl
  · by_contra h
    rw [hQn] at h
    have hL : L = l.length - 1 := by omega
    have hidx : ((s + L) % l.length + 1) % l.length = s := by
      rw [Nat.mod_add_mod, show s + L + 1 = s + l.length by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hsn]
    apply hd.not_subset_edge hQ (Nat.mod_lt _ (by omega) : (s + L) % l.length < l.length)
    unfold Polygon.edge
    rw [hQn, hidx, hv1, hv2, pairSeg, Chazelle.Geometry.segment_comm]
  · rw [hQn, Nat.mod_eq_of_lt hsn, hv1, hv2]
    exact hd.2.2.2.1

/-! ### The symmetric package of facts about the two pieces -/

/-- The facts about the two pieces `l₁`, `l₂` of `l` cut along the diagonal `d`, in a form that
is symmetric in the two pieces (`SplitPair.symm`). -/
structure SplitPair (P : Polygon) (l : List ℕ) (d : ℕ × ℕ) (l₁ l₂ : List ℕ) : Prop where
  simple₁ : (subPoly P l₁).Simple
  simple₂ : (subPoly P l₂).Simple
  cover : (subPoly P l).filled = (subPoly P l₁).filled ∪ (subPoly P l₂).filled
  meet : (subPoly P l₁).filled ∩ (subPoly P l₂).filled ⊆ pairSeg P d
  bd₁ : (subPoly P l₁).boundary ⊆ (subPoly P l).boundary ∪ pairSeg P d
  bd₂ : (subPoly P l₂).boundary ⊆ (subPoly P l).boundary ∪ pairSeg P d
  chord₁ : pairSeg P d ⊆ (subPoly P l₁).boundary
  chord₂ : pairSeg P d ⊆ (subPoly P l₂).boundary
  bd : (subPoly P l).boundary ⊆ (subPoly P l₁).boundary ∪ (subPoly P l₂).boundary
  sub₁ : ∀ x ∈ l₁, x ∈ l
  sub₂ : ∀ x ∈ l₂, x ∈ l
  vert₁ : ∀ x ∈ l, P.vtx x ∈ (subPoly P l₁).filled → x ∈ l₁
  vert₂ : ∀ x ∈ l, P.vtx x ∈ (subPoly P l₂).filled → x ∈ l₂
  edges₁ : ∀ x y, CycEdge l₁ x y → CycEdge l x y ∨ (x, y) = d ∨ (x, y) = d.swap
  edges₂ : ∀ x y, CycEdge l₂ x y → CycEdge l x y ∨ (x, y) = d ∨ (x, y) = d.swap
  len : l₁.length + l₂.length = l.length + 2

/-- The package is symmetric in the two pieces. -/
theorem SplitPair.symm {l : List ℕ} {d : ℕ × ℕ} {l₁ l₂ : List ℕ} (h : SplitPair P l d l₁ l₂) :
    SplitPair P l d l₂ l₁ where
  simple₁ := h.simple₂
  simple₂ := h.simple₁
  cover := by rw [h.cover, Set.union_comm]
  meet := by rw [Set.inter_comm]; exact h.meet
  bd₁ := h.bd₂
  bd₂ := h.bd₁
  chord₁ := h.chord₂
  chord₂ := h.chord₁
  bd := by rw [Set.union_comm]; exact h.bd
  sub₁ := h.sub₂
  sub₂ := h.sub₁
  vert₁ := h.vert₂
  vert₂ := h.vert₁
  edges₁ := h.edges₂
  edges₂ := h.edges₁
  len := by rw [Nat.add_comm]; exact h.len

/-- **The two arcs of a diagonal form a `SplitPair`** (general positions: `s` is the position of
`d.1`, and `(s + L) % n` that of `d.2`). -/
theorem splitPair_arcs {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ} (hd : IsDiag P l d)
    {s L : ℕ} (hsn : s < l.length) (hs : l.getD s 0 = d.1) (hL1 : 1 ≤ L) (hLn : L < l.length)
    (he : l.getD ((s + L) % l.length) 0 = d.2) :
    SplitPair P l d (arcList l s L) (arcList l ((s + L) % l.length) (l.length - L)) := by
  have hQn : (subPoly P l).n = l.length := n_subPoly P l
  have hdiag : IsDiagonal (subPoly P l) s L := isDiagonal_of_isDiag hQ hd hsn hs hL1 hLn he
  have hv1 : (subPoly P l).vtx (s % (subPoly P l).n) = P.vtx d.1 := by
    rw [hQn, Nat.mod_eq_of_lt hsn, vtx_subPoly_getD P l hsn, hs]
  have hv2 : (subPoly P l).vtx ((s + L) % (subPoly P l).n) = P.vtx d.2 := by
    rw [hQn, vtx_subPoly_getD P l (Nat.mod_lt _ (by omega)), he]
  have hchord : Chazelle.segment ((subPoly P l).vtx (s % (subPoly P l).n))
      ((subPoly P l).vtx ((s + L) % (subPoly P l).n)) = pairSeg P d := by
    rwr [hv1, hv2]
  have hin : Chazelle.segment ((subPoly P l).vtx (s % (subPoly P l).n))
      ((subPoly P l).vtx ((s + L) % (subPoly P l).n)) ⊆ (subPoly P l).filled := by
    rw [hchord]; exact hd.2.2.2.2
  have hn : 0 < (subPoly P l).n := by omega
  have hLQ : L ≤ (subPoly P l).n := by omega
  have e1 : subPoly P (arcList l s L) = (subPoly P l).arc s L := subPoly_arcList P l s hLn
  have e2 : subPoly P (arcList l ((s + L) % l.length) (l.length - L)) =
      (subPoly P l).arc ((s + L) % (subPoly P l).n) ((subPoly P l).n - L) := by
    rw [hQn]; exact subPoly_arcList P l _ (by omega)
  have hchord' : Chazelle.segment ((subPoly P l).vtx ((s + L) % (subPoly P l).n))
      ((subPoly P l).vtx (s % (subPoly P l).n)) = pairSeg P d := by
    rwx [Chazelle.Geometry.segment_comm]
  have hchord2 : Chazelle.segment
      ((subPoly P l).vtx (((s + L) % (subPoly P l).n + ((subPoly P l).n - L)) % (subPoly P l).n))
      ((subPoly P l).vtx ((s + L) % (subPoly P l).n % (subPoly P l).n)) = pairSeg P d := by
    rwx [Chazelle.Existence.compl_arc_last_index _ s L hLQ, Nat.mod_mod]
  have hmeet := Chazelle.Existence.filled_arcs_meet_on_chord _ s L hQ hdiag hin
  have hl1 := length_arcList (l := l) (s := s) hLn
  have hl2 := length_arcList (l := l) (s := (s + L) % l.length) (L := l.length - L) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => mem_of_mem_arcList hx,
    fun x hx => mem_of_mem_arcList hx, ?_, ?_, ?_, ?_, by omega⟩
  · rw [e1]; exact Chazelle.Existence.simple_arc _ s L hQ hdiag
  · rw [e2]; exact Chazelle.Existence.simple_arc_compl _ s L hQ hdiag
  · rw [e1, e2]; exact Chazelle.Existence.filled_eq_union_arcs _ s L hQ hdiag hin
  · rw [e1, e2, ← hchord]
    rintro p ⟨h1, h2⟩
    exact hmeet p h1 h2
  · rw [e1, ← hchord']; exact Chazelle.Existence.boundary_arc_subset _ s L hn
  · rw [e2, ← hchord2]; exact Chazelle.Existence.boundary_arc_subset _ _ _ hn
  · rw [e1, ← hchord']; exact Chazelle.Existence.chord_subset_boundary_arc _ s L
  · rw [e2, ← hchord2]; exact Chazelle.Existence.chord_subset_boundary_arc _ _ _
  · rw [e1, e2]; exact Chazelle.Existence.boundary_subset_arcs _ s L hLQ hn
  · -- vertices of `subPoly P l` filled in the first arc
    intro x hx hxf
    have hi := List.idxOf_lt_length_of_mem hx
    have hxv := vtx_idxOf P hx
    rw [e1, ← hxv] at hxf
    obtain ⟨k, hk, hkv⟩ := Chazelle.Existence.exists_arc_vertex_of_mem_filled _ s L hdiag hmeet
      (by rwx [hQn]) hxf
    rw [← e1, hxv, vtx_subPoly_getD P _ (by rwo [hl1])] at hkv
    have hmem : (arcList l s L).getD k 0 ∈ arcList l s L := by
      rw [getD_eq_getElem_of_lt _ _ (by rwo [hl1])]; exact List.getElem_mem _
    rw [← eq_of_vtx_eq P hQ (mem_of_mem_arcList hmem) hx hkv]
    exact hmem
  · -- vertices of `subPoly P l` filled in the second arc
    intro x hx hxf
    have hi := List.idxOf_lt_length_of_mem hx
    have hxv := vtx_idxOf P hx
    rw [e2, ← hxv] at hxf
    obtain ⟨k, hk, hkv⟩ := Chazelle.Existence.exists_arc_compl_vertex_of_mem_filled _ s L hdiag
      hmeet (by rwx [hQn]) hxf
    rw [← e2, hxv, vtx_subPoly_getD P _ (by rw [hl2]; rwo [hQn] at hk)] at hkv
    have hmem : (arcList l ((s + L) % l.length) (l.length - L)).getD k 0 ∈
        arcList l ((s + L) % l.length) (l.length - L) := by
      rw [getD_eq_getElem_of_lt _ _ (by rw [hl2]; rwo [hQn] at hk)]
      exact List.getElem_mem _
    rw [← eq_of_vtx_eq P hQ (mem_of_mem_arcList hmem) hx hkv]
    exact hmem
  · -- edges of the first arc
    rintro x y ⟨k, hk, rfl, rfl⟩
    rcases arcList_edge hLn hk with h | ⟨h1, h2⟩
    · exact Or.inl h
    · right; right
      rw [h1, h2, Nat.mod_eq_of_lt hsn, he, hs]
      rfl
  · -- edges of the second arc
    rintro x y ⟨k, hk, rfl, rfl⟩
    rcases arcList_edge (by omega : l.length - L < l.length) hk with h | ⟨h1, h2⟩
    · exact Or.inl h
    · right; left
      have hidx : ((s + L) % l.length + (l.length - L)) % l.length = s := by
        rw [Nat.mod_add_mod, show s + L + (l.length - L) = s + l.length by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hsn]
      rw [h1, h2, hidx, Nat.mod_mod, he, hs]

/-- Index facts for `splitFst` / `splitSnd`. -/
theorem splitSnd_eq {l : List ℕ} {d : ℕ × ℕ} (h1 : d.1 ∈ l) (h2 : d.2 ∈ l) (hne : d.1 ≠ d.2) :
    splitSnd l d = arcList l ((l.idxOf d.1 + diagLen l d) % l.length) (l.length - diagLen l d) := by
  rwr [(diagLen_spec h1 h2 hne).2.2]

/-- **Splitting along a diagonal.**  For a simple `subPoly P l` and a diagonal `d`, the pieces
`splitFst l d = [d.1, …, d.2]` and `splitSnd l d = [d.2, …, d.1]` form a `SplitPair`. -/
theorem splitPair_split {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ} (hd : IsDiag P l d) :
    SplitPair P l d (splitFst l d) (splitSnd l d) := by
  obtain ⟨hL1, hLn, hsL⟩ := diagLen_spec hd.1 hd.2.1 hd.2.2.1
  rw [splitSnd_eq hd.1 hd.2.1 hd.2.2.1]
  exact splitPair_arcs hQ hd (List.idxOf_lt_length_of_mem hd.1) (getD_idxOf hd.1) hL1 hLn
    (by rw [hsL]; exact getD_idxOf hd.2.1)

/-! ### Consequences of the package -/

section Consequences

variable {l : List ℕ} {d : ℕ × ℕ} {l₁ l₂ : List ℕ}

/-- The filled region of the first piece lies in that of `subPoly P l`. -/
theorem SplitPair.filled_subset (h : SplitPair P l d l₁ l₂) :
    (subPoly P l₁).filled ⊆ (subPoly P l).filled := by
  rw [h.cover]; exact Set.subset_union_left

/-- The interior of the first piece does not meet the filled region of the second. -/
theorem SplitPair.interior_not_mem_filled (h : SplitPair P l d l₁ l₂) {p : Point}
    (hp : p ∈ interior (subPoly P l₁).filled) : p ∉ (subPoly P l₂).filled := by
  rw [interior_filled h.simple₁] at hp
  intro hp2
  exact hp.2 (h.chord₁ (h.meet ⟨hp.1, hp2⟩))

/-- The interior of the first piece avoids the diagonal. -/
theorem SplitPair.interior_not_mem_chord (h : SplitPair P l d l₁ l₂) {p : Point}
    (hp : p ∈ interior (subPoly P l₁).filled) : p ∉ pairSeg P d := by
  rw [interior_filled h.simple₁] at hp
  exact fun hc => hp.2 (h.chord₁ hc)

/-- The interior of the first piece avoids the boundary of `subPoly P l`. -/
theorem SplitPair.interior_not_mem_boundary (h : SplitPair P l d l₁ l₂) {p : Point}
    (hp : p ∈ interior (subPoly P l₁).filled) : p ∉ (subPoly P l).boundary := by
  intro hb
  rcases h.bd hb with h1 | h2
  · rw [interior_filled h.simple₁] at hp
    exact hp.2 h1
  · exact h.interior_not_mem_filled hp (Chazelle.Jordan.boundary_subset_filled _ h2)

/-- The open segment of another diagonal `d'` not crossing `d` lies in the open interior of one
of the two pieces (it is connected and lies in the union of the two disjoint open interiors). -/
theorem SplitPair.innerSeg_cases (h : SplitPair P l d l₁ l₂) (hQ : (subPoly P l).Simple)
    {d' : ℕ × ℕ} (hd' : IsDiag P l d') (hnc : NonCross P d d') :
    innerSeg (P.vtx d'.1) (P.vtx d'.2) ⊆ (subPoly P l₁).filled \ (subPoly P l₁).boundary ∨
      innerSeg (P.vtx d'.1) (P.vtx d'.2) ⊆ (subPoly P l₂).filled \ (subPoly P l₂).boundary := by
  have hne := hd'.vtx_ne P hQ
  apply IsPreconnected.subset_or_subset (isOpen_filled_sdiff_boundary h.simple₁)
    (isOpen_filled_sdiff_boundary h.simple₂) ?_ ?_ (isPreconnected_innerSeg _ _)
  · rw [Set.disjoint_left]
    rintro p ⟨hp1, hpb1⟩ ⟨hp2, -⟩
    exact hpb1 (h.chord₁ (h.meet ⟨hp1, hp2⟩))
  · intro p hp
    have hps := innerSeg_subset _ _ hp
    obtain ⟨hpa, hpb⟩ := ne_of_mem_innerSeg hne hp
    have hpQ  := hd'.2.2.2.1 p hps hpa hpb
    have hpc : p ∉ pairSeg P d := by
      intro hpc
      rcases (hnc ⟨hpc, hps⟩).2 with e | e
      · exact hpa e
      · exact hpb e
    have hpf  := hd'.2.2.2.2 hps
    rw [h.cover] at hpf
    rcases hpf with hf | hf
    · left
      refine ⟨hf, fun hb => ?_⟩
      rcases h.bd₁ hb with hb' | hb'
      · exact hpQ hb'
      · exact hpc hb'
    · right
      refine ⟨hf, fun hb => ?_⟩
      rcases h.bd₂ hb with hb' | hb'
      · exact hpQ hb'
      · exact hpc hb'

/-- If the open segment of a diagonal `d'` of `subPoly P l` lies in the open interior of the
first piece, then `d'` is a diagonal of the first piece. -/
theorem SplitPair.isDiag_of_innerSeg_subset (h : SplitPair P l d l₁ l₂) {d' : ℕ × ℕ}
    (hd' : IsDiag P l d')
    (hsub : innerSeg (P.vtx d'.1) (P.vtx d'.2) ⊆
      (subPoly P l₁).filled \ (subPoly P l₁).boundary) :
    IsDiag P l₁ d' := by
  have hseg : pairSeg P d' ⊆ (subPoly P l₁).filled := by
    intro p hp
    have := closure_mono (hsub.trans Set.sdiff_subset) (segment_subset_closure_innerSeg _ _ hp)
    exact (isClosed_filled _).closure_subset this
  refine ⟨h.vert₁ _ hd'.1 (hseg (Chazelle.Geometry.left_mem_segment _ _)),
    h.vert₁ _ hd'.2.1 (hseg (Chazelle.Geometry.right_mem_segment _ _)), hd'.2.2.1, ?_, hseg⟩
  intro p hp hpa hpb
  exact (hsub (mem_innerSeg_of_ne hp hpa hpb)).2

/-- No diagonal `d'` not crossing `d` has both endpoints in both pieces (its segment would lie on
the segment of `d`). -/
theorem SplitPair.not_mem_both (h : SplitPair P l d l₁ l₂) (hQ : (subPoly P l).Simple)
    {d' : ℕ × ℕ} (hd' : IsDiag P l d') (hnc : NonCross P d d') (h1 : d'.1 ∈ l₁ ∧ d'.2 ∈ l₁)
    (h2 : d'.1 ∈ l₂ ∧ d'.2 ∈ l₂) : False := by
  have hne := hd'.vtx_ne P hQ
  have hv : ∀ x, x ∈ l₁ → x ∈ l₂ → P.vtx x ∈ pairSeg P d := fun x hx1 hx2 =>
    h.meet ⟨Chazelle.Jordan.boundary_subset_filled _ (vtx_mem_boundary_subPoly P hx1),
      Chazelle.Jordan.boundary_subset_filled _ (vtx_mem_boundary_subPoly P hx2)⟩
  have hsub : pairSeg P d' ⊆ pairSeg P d :=
    Chazelle.Geometry.segment_subset_of_convex (Chazelle.Geometry.segment_convex _ _)
      (hv _ h1.1 h2.1) (hv _ h1.2 h2.2)
  obtain ⟨p, hp⟩ := innerSeg_nonempty (P.vtx d'.1) (P.vtx d'.2)
  obtain ⟨hpa, hpb⟩ := ne_of_mem_innerSeg hne hp
  have hps := innerSeg_subset _ _ hp
  rcases (hnc ⟨hsub hps, hps⟩).2 with e | e
  · exact hpa e
  · exact hpb e

/-- **Distributing the other diagonals, first piece.**  A diagonal `d'` of `subPoly P l` not
crossing `d` whose endpoints both lie in the first piece is a diagonal of the first piece. -/
theorem SplitPair.isDiag_fst (h : SplitPair P l d l₁ l₂) (hQ : (subPoly P l).Simple)
    {d' : ℕ × ℕ} (hd' : IsDiag P l d') (hnc : NonCross P d d') (hmem : d'.1 ∈ l₁ ∧ d'.2 ∈ l₁) :
    IsDiag P l₁ d' := by
  rcases h.innerSeg_cases hQ hd' hnc with hs | hs
  · exact h.isDiag_of_innerSeg_subset hd' hs
  · have := h.symm.isDiag_of_innerSeg_subset hd' hs
    exact (h.not_mem_both hQ hd' hnc hmem ⟨this.1, this.2.1⟩).elim

/-- **Distributing the other diagonals, second piece.**  A diagonal `d'` of `subPoly P l` not
crossing `d` whose endpoints do not both lie in the first piece is a diagonal of the second
piece. -/
theorem SplitPair.isDiag_snd (h : SplitPair P l d l₁ l₂) (hQ : (subPoly P l).Simple)
    {d' : ℕ × ℕ} (hd' : IsDiag P l d') (hnc : NonCross P d d')
    (hmem : ¬ (d'.1 ∈ l₁ ∧ d'.2 ∈ l₁)) : IsDiag P l₂ d' := by
  rcases h.innerSeg_cases hQ hd' hnc with hs | hs
  · have := h.isDiag_of_innerSeg_subset hd' hs
    exact (hmem ⟨this.1, this.2.1⟩).elim
  · exact h.symm.isDiag_of_innerSeg_subset hd' hs

/-- The interiors of the filled regions of the two pieces are disjoint. -/
theorem SplitPair.interior_disjoint (h : SplitPair P l d l₁ l₂) :
    Disjoint (interior (subPoly P l₁).filled) (interior (subPoly P l₂).filled) :=
  Set.disjoint_left.2 fun _ hp hp2 => h.interior_not_mem_filled hp (interior_subset hp2)

end Consequences

/-- **Distributing a non-crossing diagonal.**  Let `subPoly P l` be simple, `d` a diagonal and
`d'` another diagonal not crossing `d`.  Either both endpoints of `d'` are entries of the first
piece `splitFst l d` and `d'` is a diagonal of it, or they are not both entries of the first piece,
both are entries of the second piece `splitSnd l d`, and `d'` is a diagonal of it. -/
theorem isDiag_split_cases {l : List ℕ} (hQ : (subPoly P l).Simple) {d d' : ℕ × ℕ}
    (hd : IsDiag P l d) (hd' : IsDiag P l d') (hnc : NonCross P d d') :
    (d'.1 ∈ splitFst l d ∧ d'.2 ∈ splitFst l d ∧ IsDiag P (splitFst l d) d') ∨
      (¬ (d'.1 ∈ splitFst l d ∧ d'.2 ∈ splitFst l d) ∧ d'.1 ∈ splitSnd l d ∧
        d'.2 ∈ splitSnd l d ∧ IsDiag P (splitSnd l d) d') := by
  have hs := splitPair_split hQ hd
  by_cases hmem : d'.1 ∈ splitFst l d ∧ d'.2 ∈ splitFst l d
  · exact Or.inl ⟨hmem.1, hmem.2, hs.isDiag_fst hQ hd' hnc hmem⟩
  · have h2 := hs.isDiag_snd hQ hd' hnc hmem
    exact Or.inr ⟨hmem, h2.1, h2.2.1, h2⟩

/-! ### Combining weak triangulations of the two pieces -/

/-- The indices of the triangles of a weak triangulation are in range. -/
theorem index_lt_of_weak {Q : Polygon} {T : List Polygon.Triangle} (h : WeakTriangulates Q T)
    {t : Polygon.Triangle} (ht : t ∈ T) : t.1 < Q.n ∧ t.2.1 < Q.n ∧ t.2.2 < Q.n := by
  obtain ⟨h1, h2, h3, -⟩ := h.1 t ht
  exact ⟨h1, h2, h3⟩

/-- **Combining along one diagonal.**  Weak triangulations `T₁` of `subPoly P (splitFst l d)` and
`T₂` of `subPoly P (splitSnd l d)` (in positions of the pieces) relabel to a weak triangulation of
`subPoly P l` (in positions of `l`): position `k` of the first piece is position
`(idx d.1 + k) % n` of `l`, position `k` of the second is `(idx d.2 + k) % n`. -/
theorem weakTriangulates_split {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ}
    (hd : IsDiag P l d) {T₁ T₂ : List Polygon.Triangle}
    (h₁ : WeakTriangulates (subPoly P (splitFst l d)) T₁)
    (h₂ : WeakTriangulates (subPoly P (splitSnd l d)) T₂) :
    WeakTriangulates (subPoly P l)
      (T₁.map (relabel (l.idxOf d.1) l.length) ++ T₂.map (relabel (l.idxOf d.2) l.length)) := by
  obtain ⟨hL1, hLn, hsL⟩ := diagLen_spec hd.1 hd.2.1 hd.2.2.1
  have hsn := List.idxOf_lt_length_of_mem hd.1
  have hQn  := n_subPoly P l
  have hdiag := isDiagonal_of_isDiag hQ hd hsn (getD_idxOf hd.1) hL1 hLn
    (by rw [hsL]; exact getD_idxOf hd.2.1)
  have hin : Chazelle.segment ((subPoly P l).vtx (l.idxOf d.1 % (subPoly P l).n))
      ((subPoly P l).vtx ((l.idxOf d.1 + diagLen l d) % (subPoly P l).n)) ⊆
        (subPoly P l).filled := by
    rw [hQn, Nat.mod_eq_of_lt hsn, hsL, vtx_idxOf P hd.1, vtx_idxOf P hd.2.1]
    exact hd.2.2.2.2
  have e1 : subPoly P (splitFst l d) = (subPoly P l).arc (l.idxOf d.1) (diagLen l d) :=
    subPoly_arcList P l _ hLn
  have e2 : subPoly P (splitSnd l d) = (subPoly P l).arc
      ((l.idxOf d.1 + diagLen l d) % (subPoly P l).n) ((subPoly P l).n - diagLen l d) := by
    rw [hQn, hsL]; exact subPoly_arcList P l _ (by omega)
  rw [e1] at h₁
  rw [e2] at h₂
  have := Chazelle.Existence.weakTriangulates_of_diagonal hQ hdiag hin h₁ h₂
  rwa [hQn, hsL] at this

/-- Relabelling a triangle of an arc of `l` (positions `≤ L`) to positions of `l` and then to
original indices agrees with relabelling it directly to original indices. -/
theorem relabelList_relabel_arc {l : List ℕ} {s L : ℕ} (hL : L < l.length) {t : Polygon.Triangle}
    (ht : t.1 ≤ L ∧ t.2.1 ≤ L ∧ t.2.2 ≤ L) :
    relabelList l (relabel s l.length t) = relabelList (arcList l s L) t := by
  obtain ⟨a, b, c⟩ := t
  simp only [relabelList, Chazelle.Existence.relabel_fst, Chazelle.Existence.relabel_snd_fst,
    Chazelle.Existence.relabel_snd_snd]
  rw [getD_arcList hL ht.1, getD_arcList hL ht.2.1, getD_arcList hL ht.2.2]

/-- `relabelList_relabel_arc` for the first piece. -/
theorem relabelList_relabel_fst {l : List ℕ} {d : ℕ × ℕ} (h1 : d.1 ∈ l) (h2 : d.2 ∈ l)
    (hne : d.1 ≠ d.2) {t : Polygon.Triangle}
    (ht : t.1 < (splitFst l d).length ∧ t.2.1 < (splitFst l d).length ∧
      t.2.2 < (splitFst l d).length) :
    relabelList l (relabel (l.idxOf d.1) l.length t) = relabelList (splitFst l d) t := by
  obtain ⟨-, hLn, -⟩ := diagLen_spec h1 h2 hne
  have hlen : (splitFst l d).length = diagLen l d + 1 := length_arcList hLn
  rw [hlen] at ht
  exact relabelList_relabel_arc hLn ⟨by omega, by omega, by omega⟩

/-- `relabelList_relabel_arc` for the second piece. -/
theorem relabelList_relabel_snd {l : List ℕ} {d : ℕ × ℕ} (h1 : d.1 ∈ l) (h2 : d.2 ∈ l)
    (hne : d.1 ≠ d.2) {t : Polygon.Triangle}
    (ht : t.1 < (splitSnd l d).length ∧ t.2.1 < (splitSnd l d).length ∧
      t.2.2 < (splitSnd l d).length) :
    relabelList l (relabel (l.idxOf d.2) l.length t) = relabelList (splitSnd l d) t := by
  obtain ⟨hL1, hLn, -⟩ := diagLen_spec h1 h2 hne
  have hlt : l.length - diagLen l d < l.length := by omega
  have hlen : (splitSnd l d).length = l.length - diagLen l d + 1 := length_arcList hlt
  rw [hlen] at ht
  exact relabelList_relabel_arc hlt ⟨by omega, by omega, by omega⟩

end

end Chazelle.Split
