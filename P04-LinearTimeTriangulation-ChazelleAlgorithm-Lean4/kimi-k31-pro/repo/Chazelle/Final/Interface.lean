module

public import Chazelle.Mountain.Decompose
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# The interface between the visibility-map stage and the final triangulation stage

The visibility-map stage hands over two finite tables:

* the **trapezoid table** `T : TrapTable`, a list of records `TrapRec` = (left side edge,
  right side edge, top vertex, bottom vertex), one per region of the horizontal visibility map
  (`IsTrapTable P T`);
* the **vertex-chord table** `C : List ChordRec`, a list of records (source vertex, direction,
  target vertex), one per vertex-to-vertex chord and direction (`IsVtxChordTable P C`).

From these, the final stage computes the list of inserted diagonals
`diagList P T C : List (ℕ × ℕ)`: the pairs `(top, bot)` of the records whose top and bottom
vertices are not adjacent, followed by the pairs `(src, dst)` of the chord records, each
normalised as an unordered pair (`sortPair`, smaller index first) and deduplicated.

## Main results

* `trapRecOf_eq_iff`: the record of a trapezoid depends only on its region (in particular the
  side edges `i`, `j` are determined by the region: `left_eq_of_region_eq`,
  `right_eq_of_region_eq`), and conversely the record determines the region
  (`TrapRec.region_trapRecOf`).
* `isTrapTable_iff`: a trapezoid table is exactly a duplicate-free list whose members are the
  records of the trapezoid data of `P`.
* `diagList_spec`, `diagList_mem_iff`: the members of `diagList P T C` are exactly the inserted
  diagonals `allDiagonals P` as unordered pairs; `diagList_nodup`; `diagList_length_le`: at most
  `4 n + 1` of them.
* `exists_trapTable`, `exists_vtxChordTable`: both tables exist for every simple polygon.
-/

namespace Chazelle.Final

@[expose] public section

open Set
open Chazelle.Jordan (simple_vtx_inj simple_edge_inter)
open Chazelle.Visibility
open Chazelle.Mountain

/-! ### The trapezoid table -/

/-- A record of the trapezoid table: the indices of the left and right side edges and of the top
and bottom vertices of a trapezoid. -/
structure TrapRec where
  /-- The left side edge. -/
  left : ℕ
  /-- The right side edge. -/
  right : ℕ
  /-- The top vertex (leftmost vertex of the closed top side). -/
  top : ℕ
  /-- The bottom vertex (rightmost vertex of the closed bottom side). -/
  bot : ℕ
  deriving DecidableEq

/-- The trapezoid table handed over by the visibility-map stage. -/
abbrev TrapTable : Type := List TrapRec

/-- The record of trapezoid data. -/
noncomputable def trapRecOf {P : Polygon} (D : TrapData P) : TrapRec := ⟨D.i, D.j, D.top, D.bot⟩

/-- **Validity of a trapezoid table.**  `T` is the list of records of a list `L` of trapezoid
data whose regions are pairwise distinct and are exactly the regions of the visibility map; so
the records are in bijection with the regions, and the record of a region `R` is
`⟨D.i, D.j, D.top, D.bot⟩` for trapezoid data `D` with `D.region = R` (which data is used does
not matter: `trapRecOf_eq_of_region_eq`). -/
def IsTrapTable (P : Polygon) (T : TrapTable) : Prop :=
  ∃ L : List (TrapData P), L.map trapRecOf = T ∧ (L.map TrapData.region).Nodup ∧
    ∀ R, R ∈ regions P ↔ ∃ D ∈ L, D.region = R

/-! ### The record depends only on the region -/

/-- Two trapezoid data with the same region have the same heights. -/
theorem heights_eq_of_region_eq {P : Polygon} (hP : P.Simple) (D D' : TrapData P)
    (h : D.region = D'.region) : D.y₁ = D'.y₁ ∧ D.y₂ = D'.y₂ := by
  have hd := TrapData.diag_eq_of_region_eq hP D D' h
  have htop : D.top = D'.top := congrArg Prod.fst hd
  have hbot : D.bot = D'.bot := congrArg Prod.snd hd
  exact ⟨by rw [← D.bot_snd hP, ← D'.bot_snd hP, hbot],
    by rw [← D.top_snd hP, ← D'.top_snd hP, htop]⟩

/-- A point on the line of a side edge, strictly inside the height range, is not a vertex
unless it is off the closed corridor; used to separate two side edges. -/
theorem not_vtx_on_side {P : Polygon} (D : TrapData P) {y : ℝ}
    (h1 : D.y₁ < y) (h2 : y < D.y₂) {x : ℝ} (hx1 : edgeX P D.i y ≤ x) (hx2 : x ≤ edgeX P D.j y)
    {m : ℕ} (hm : m < P.n) (hmp : P.vtx m = (x, y)) : False := by
  have e1 : (P.vtx m).1 = x := by rw [hmp]
  have e2 : (P.vtx m).2 = y := by rw [hmp]
  exact D.isTrap.no_vertex m hm (by rwx [e2]) (by rwx [e2])
    (by rwx [e1, e2]) (by rwx [e1, e2])

/-- A point of two distinct edges of a simple polygon is a vertex. -/
theorem exists_vtx_of_mem_two_edges {P : Polygon} (hP : P.Simple) {a b : ℕ} (ha : a < P.n)
    (hb : b < P.n) (hab : a ≠ b) {p : Point} (hpa : p ∈ P.edge a) (hpb : p ∈ P.edge b) :
    ∃ m < P.n, P.vtx m = p := by
  have hc : p ∈ P.commonEndpoints a b := by
    rw [← simple_edge_inter hP ha hb hab]; exact ⟨hpa, hpb⟩
  rcases hc.1 with e | e
  · exact ⟨a, ha, e.symm⟩
  · exact ⟨(a + 1) % P.n, Nat.mod_lt _ (by omega), e.symm⟩

/-- **The left side edge depends only on the region.** -/
theorem left_eq_of_region_eq {P : Polygon} (hP : P.Simple) (D D' : TrapData P)
    (h : D.region = D'.region) : D.i = D'.i := by
  obtain ⟨hy1, hy2⟩ := heights_eq_of_region_eq hP D D' h
  have h12 : D.y₁ < D.y₂ := D.isTrap.bot_lt.trans D.isTrap.lt_top
  set y := (D.y₁ + D.y₂) / 2 with hydef
  have hyl : D.y₁ < y := by rwli [hydef]
  have hyr : y < D.y₂ := by rwli [hydef]
  have hy : y ∈ Icc D.y₁ D.y₂ := ⟨hyl.le, hyr.le⟩
  have hy' : y ∈ Icc D'.y₁ D'.y₂ := by rwx [← hy1, ← hy2]
  have e1 := D.isTrap.left_le_of_subset hP D.free D'.isTrap h.subset y hy
  have e2 := D'.isTrap.left_le_of_subset hP D'.free D.isTrap h.symm.subset y hy'
  have heq : edgeX P D.i y = edgeX P D'.i y := le_antisymm e2 e1
  by_contra hne
  have hp1 : ((edgeX P D.i y, y) : Point) ∈ P.edge D.i := D.isTrap.mem_edgeL hy.1 hy.2 rfl
  have hp2 : ((edgeX P D.i y, y) : Point) ∈ P.edge D'.i :=
    D'.isTrap.mem_edgeL hy'.1 hy'.2 heq
  obtain ⟨m, hm, hmp⟩ := exists_vtx_of_mem_two_edges hP D.isTrap.hi D'.isTrap.hi hne hp1 hp2
  have hlt := D.isTrap.edgeX_lt hP D.free hyl hyr
  exact not_vtx_on_side D hyl hyr le_rfl hlt.le hm hmp

/-- **The right side edge depends only on the region.** -/
theorem right_eq_of_region_eq {P : Polygon} (hP : P.Simple) (D D' : TrapData P)
    (h : D.region = D'.region) : D.j = D'.j := by
  obtain ⟨hy1, hy2⟩ := heights_eq_of_region_eq hP D D' h
  have h12 : D.y₁ < D.y₂ := D.isTrap.bot_lt.trans D.isTrap.lt_top
  set y := (D.y₁ + D.y₂) / 2 with hydef
  have hyl : D.y₁ < y := by rwli [hydef]
  have hyr : y < D.y₂ := by rwli [hydef]
  have hy : y ∈ Icc D.y₁ D.y₂ := ⟨hyl.le, hyr.le⟩
  have hy' : y ∈ Icc D'.y₁ D'.y₂ := by rwx [← hy1, ← hy2]
  have e1 := D.isTrap.right_le_of_subset hP D.free D'.isTrap h.subset y hy
  have e2 := D'.isTrap.right_le_of_subset hP D'.free D.isTrap h.symm.subset y hy'
  have heq : edgeX P D.j y = edgeX P D'.j y := le_antisymm e1 e2
  by_contra hne
  have hp1 : ((edgeX P D.j y, y) : Point) ∈ P.edge D.j := D.isTrap.mem_edgeR hy.1 hy.2 rfl
  have hp2 : ((edgeX P D.j y, y) : Point) ∈ P.edge D'.j :=
    D'.isTrap.mem_edgeR hy'.1 hy'.2 heq
  obtain ⟨m, hm, hmp⟩ := exists_vtx_of_mem_two_edges hP D.isTrap.hj D'.isTrap.hj hne hp1 hp2
  have hlt := D.isTrap.edgeX_lt hP D.free hyl hyr
  exact not_vtx_on_side D hyl hyr hlt.le le_rfl hm hmp

/-- **The record depends only on the region.** -/
theorem trapRecOf_eq_of_region_eq {P : Polygon} (hP : P.Simple) (D D' : TrapData P)
    (h : D.region = D'.region) : trapRecOf D = trapRecOf D' := by
  have hd := TrapData.diag_eq_of_region_eq hP D D' h
  show (⟨D.i, D.j, D.top, D.bot⟩ : TrapRec) = ⟨D'.i, D'.j, D'.top, D'.bot⟩
  rw [left_eq_of_region_eq hP D D' h, right_eq_of_region_eq hP D D' h,
    show D.top = D'.top from congrArg Prod.fst hd, show D.bot = D'.bot from congrArg Prod.snd hd]

/-! ### Properties of a trapezoid table -/

/-- The records of a trapezoid table are the records of trapezoid data. -/
theorem IsTrapTable.exists_of_mem {P : Polygon} {T : TrapTable} (hT : IsTrapTable P T)
    {r : TrapRec} (hr : r ∈ T) : ∃ D : TrapData P, trapRecOf D = r := by
  obtain ⟨L, rfl, -, -⟩ := hT
  obtain ⟨D, -, rfl⟩ := List.mem_map.1 hr
  exact ⟨D, rfl⟩

/-- The record of any trapezoid data is in a trapezoid table. -/
theorem IsTrapTable.mem_of_trapData {P : Polygon} (hP : P.Simple) {T : TrapTable}
    (hT : IsTrapTable P T) (D : TrapData P) : trapRecOf D ∈ T := by
  obtain ⟨L, rfl, -, hreg⟩ := hT
  obtain ⟨D', hD', hreg'⟩ := (hreg D.region).1 (D.region_mem_regions hP)
  rw [← trapRecOf_eq_of_region_eq hP D' D hreg']
  exact List.mem_map_of_mem hD'

/-- **A trapezoid table has one record per region.** -/
theorem IsTrapTable.length_eq {P : Polygon} {T : TrapTable}
    (hT : IsTrapTable P T) : T.length = (regions P).ncard := by
  classical
  obtain ⟨L, rfl, hnd, hreg⟩ := hT
  have hset : ((L.map TrapData.region).toFinset : Set (Set Point)) = regions P := by
    ext R
    rw [Finset.mem_coe, List.mem_toFinset, hreg, List.mem_map]
  rw [List.length_map, ← hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd,
    List.length_map]

/-- A trapezoid table has at most `2 n + 1` records. -/
theorem IsTrapTable.length_le {P : Polygon} (hP : P.Simple) {T : TrapTable}
    (hT : IsTrapTable P T) : T.length ≤ 2 * P.n + 1 := by
  rw [hT.length_eq]
  exact regions_ncard_le hP

/-! ### The vertex-chord table -/

/-- The horizontal direction coded by a boolean: `true` is right (`1`), `false` is left (`-1`). -/
noncomputable def dirSign (b : Bool) : ℝ := if b then 1 else -1

/-- A coded direction is `1` or `-1`. -/
theorem dirSign_cases (b : Bool) : dirSign b = 1 ∨ dirSign b = -1 := by
  cases b
  · right; rfl
  · left; rfl

/-- A record of the vertex-chord table: the chord of vertex `src` in direction `dir` ends at
vertex `dst`. -/
structure ChordRec where
  /-- The vertex emitting the chord. -/
  src : ℕ
  /-- The direction (`true` = right). -/
  dir : Bool
  /-- The vertex where the chord ends. -/
  dst : ℕ
  deriving DecidableEq

/-- The record describes a vertex-to-vertex chord: the direction is locally interior at `src`
and the chord ends at vertex `dst`. -/
def ChordRec.Valid (P : Polygon) (c : ChordRec) : Prop :=
  c.src < P.n ∧ c.dst < P.n ∧ DirInterior P c.src (dirSign c.dir) ∧
    chordEnd P c.src (dirSign c.dir) = P.vtx c.dst

/-- **Validity of a vertex-chord table**: its members are exactly the valid records, and each
pair (source, direction) occurs once. -/
def IsVtxChordTable (P : Polygon) (C : List ChordRec) : Prop :=
  (∀ c, c ∈ C ↔ c.Valid P) ∧ (C.map fun c => (c.src, c.dir)).Nodup

/-- The index pairs of the valid records are exactly the vertex-to-vertex chords. -/
theorem mem_vtxChords_iff_chordRec {P : Polygon} {d : ℕ × ℕ} :
    d ∈ vtxChords P ↔ ∃ c : ChordRec, c.Valid P ∧ (c.src, c.dst) = d := by
  constructor
  · rintro ⟨h1, h2, σ, hσ, hdir, hend⟩
    rcases hσ with rfl | rfl
    · exact ⟨⟨d.1, true, d.2⟩, ⟨h1, h2, hdir, hend⟩, rfl⟩
    · exact ⟨⟨d.1, false, d.2⟩, ⟨h1, h2, hdir, hend⟩, rfl⟩
  · rintro ⟨c, ⟨h1, h2, hdir, hend⟩, rfl⟩
    exact ⟨h1, h2, dirSign c.dir, dirSign_cases c.dir, hdir, hend⟩

/-- A vertex-chord table has at most `2 n` records. -/
theorem IsVtxChordTable.length_le {P : Polygon} {C : List ChordRec} (hC : IsVtxChordTable P C) :
    C.length ≤ 2 * P.n := by
  obtain ⟨hmem, hnd⟩ := hC
  have h1 : (C.map fun c => (c.src, c.dir)).toFinset.card = C.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  have h2 : (C.map fun c => (c.src, c.dir)).toFinset ⊆
      Finset.range P.n ×ˢ (Finset.univ : Finset Bool) := by
    intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [Finset.mem_product, Finset.mem_range]
    exact ⟨((hmem c).1 hc).1, Finset.mem_univ _⟩
  have h3 := Finset.card_le_card h2
  rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool, h1] at h3
  omega

/-! ### The final-stage input: the list of inserted diagonals -/

/-- Normalise an index pair as an unordered pair: smaller index first. -/
def sortPair (d : ℕ × ℕ) : ℕ × ℕ := (min d.1 d.2, max d.1 d.2)

/-- The normal form of a pair with distinct entries is the pair or its swap, ordered strictly. -/
theorem sortPair_eq_iff {e d : ℕ × ℕ} (he : e.1 ≠ e.2) :
    sortPair e = d ↔ d.1 < d.2 ∧ (e = d ∨ e = d.swap) := by
  obtain ⟨a, b⟩ := e
  obtain ⟨x, y⟩ := d
  simp [sortPair, Prod.mk.injEq, Prod.swap_prod_mk] at he ⊢
  constructor
  · rintro ⟨rfl, rfl⟩
    rcases lt_or_gt_of_ne he with h | h
    · refine ⟨by rwx [min_eq_left h.le, max_eq_right h.le], Or.inl ?_⟩
      rw [min_eq_left h.le, max_eq_right h.le]; exact ⟨rfl, rfl⟩
    · refine ⟨by rwx [min_eq_right h.le, max_eq_left h.le], Or.inr ?_⟩
      rw [min_eq_right h.le, max_eq_left h.le]; exact ⟨rfl, rfl⟩
  · rintro ⟨hxy, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨min_eq_left hxy.le, max_eq_right hxy.le⟩
    · exact ⟨min_eq_right hxy.le, max_eq_left hxy.le⟩

/-- Whether the top and bottom vertices of a record are non-adjacent in a polygon with `n`
vertices. -/
def TrapRec.nonAdj (n : ℕ) (r : TrapRec) : Bool :=
  decide (r.bot ≠ (r.top + 1) % n ∧ r.top ≠ (r.bot + 1) % n)

/-- The pairs `(top, bot)` of the records with non-adjacent top and bottom vertices. -/
def trapPairs (P : Polygon) (T : TrapTable) : List (ℕ × ℕ) :=
  (T.filter (TrapRec.nonAdj P.n)).map fun r => (r.top, r.bot)

/-- The pairs `(src, dst)` of the chord records. -/
def chordPairs (C : List ChordRec) : List (ℕ × ℕ) := C.map fun c => (c.src, c.dst)

/-- **The list of inserted diagonals** computed by the final stage from the two tables: the
trapezoid pairs followed by the chord pairs, normalised as unordered pairs and deduplicated. -/
def diagList (P : Polygon) (T : TrapTable) (C : List ChordRec) : List (ℕ × ℕ) :=
  ((trapPairs P T ++ chordPairs C).map sortPair).dedup

/-- The trapezoid pairs of a valid table are exactly the trapezoid diagonals. -/
theorem mem_trapPairs_iff {P : Polygon} (hP : P.Simple) {T : TrapTable} (hT : IsTrapTable P T)
    {d : ℕ × ℕ} : d ∈ trapPairs P T ↔ d ∈ trapDiagonals P := by
  unfold trapPairs
  rw [List.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    rw [List.mem_filter] at hr
    obtain ⟨D, rfl⟩ := hT.exists_of_mem hr.1
    refine ⟨D, ?_, rfl⟩
    have h  := hr.2
    have h2 := of_decide_eq_true h
    exact h2
  · rintro ⟨D, hD, rfl⟩
    refine ⟨trapRecOf D, List.mem_filter.2 ⟨hT.mem_of_trapData hP D, ?_⟩, rfl⟩
    show decide (D.bot ≠ (D.top + 1) % P.n ∧ D.top ≠ (D.bot + 1) % P.n) = true
    exact decide_eq_true hD

/-- The chord pairs of a valid table are exactly the vertex-to-vertex chords. -/
theorem mem_chordPairs_iff {P : Polygon} {C : List ChordRec} (hC : IsVtxChordTable P C)
    {d : ℕ × ℕ} : d ∈ chordPairs C ↔ d ∈ vtxChords P := by
  unfold chordPairs
  rw [List.mem_map, mem_vtxChords_iff_chordRec]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (hC.1 c).1 hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (hC.1 c).2 hc, rfl⟩

/-- The concatenated pairs are exactly the inserted diagonals. -/
theorem mem_pairs_iff {P : Polygon} (hP : P.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) {d : ℕ × ℕ} :
    d ∈ trapPairs P T ++ chordPairs C ↔ d ∈ allDiagonals P := by
  rw [List.mem_append, mem_trapPairs_iff hP hT, mem_chordPairs_iff hC]
  rfl

/-- **Specification of the final-stage input**: the members of `diagList P T C` are exactly the
normal forms (as unordered pairs) of the inserted diagonals `allDiagonals P`. -/
theorem diagList_spec {P : Polygon} (hP : P.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) (d : ℕ × ℕ) :
    d ∈ diagList P T C ↔ ∃ e ∈ allDiagonals P, sortPair e = d := by
  unfold diagList
  rw [List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, (mem_pairs_iff hP hT hC).1 he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, (mem_pairs_iff hP hT hC).2 he, rfl⟩

/-- **Membership in the final-stage input**: `d ∈ diagList P T C` iff `d.1 < d.2` and `d` or
its swap is an inserted diagonal. -/
theorem diagList_mem_iff {P : Polygon} (hP : P.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) (d : ℕ × ℕ) :
    d ∈ diagList P T C ↔ d.1 < d.2 ∧ (d ∈ allDiagonals P ∨ d.swap ∈ allDiagonals P) := by
  rw [diagList_spec hP hT hC]
  constructor
  · rintro ⟨e, he, hed⟩
    rw [sortPair_eq_iff (allDiagonals_lt hP he).2.2] at hed
    obtain ⟨hlt, rfl | rfl⟩ := hed
    · exact ⟨hlt, Or.inl he⟩
    · exact ⟨hlt, Or.inr he⟩
  · rintro ⟨hlt, h | h⟩
    · exact ⟨d, h, (sortPair_eq_iff (allDiagonals_lt hP h).2.2).2 ⟨hlt, Or.inl rfl⟩⟩
    · exact ⟨d.swap, h, (sortPair_eq_iff (allDiagonals_lt hP h).2.2).2 ⟨hlt, Or.inr rfl⟩⟩

/-- The members of the final-stage input are pairs of distinct vertex indices, smaller first. -/
theorem diagList_lt {P : Polygon} (hP : P.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) {d : ℕ × ℕ} (hd : d ∈ diagList P T C) :
    d.1 < d.2 ∧ d.2 < P.n := by
  obtain ⟨hlt, h | h⟩ := (diagList_mem_iff hP hT hC d).1 hd
  · exact ⟨hlt, (allDiagonals_lt hP h).2.1⟩
  · exact ⟨hlt, (allDiagonals_lt hP h).1⟩

/-- **No duplicates** (as unordered pairs: every member is in normal form). -/
theorem diagList_nodup (P : Polygon) (T : TrapTable) (C : List ChordRec) :
    (diagList P T C).Nodup :=
  List.nodup_dedup _

/-- **At most `4 n + 1` inserted diagonals are handed to the final stage.** -/
theorem diagList_length_le {P : Polygon} (hP : P.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) :
    (diagList P T C).length ≤ 4 * P.n + 1 := by
  unfold diagList
  have h1 := (List.dedup_sublist ((trapPairs P T ++ chordPairs C).map sortPair)).length_le
  have h2 : (trapPairs P T).length ≤ T.length := by
    unfold trapPairs
    rw [List.length_map]
    exact List.length_filter_le _ _
  have h3 : (chordPairs C).length = C.length := List.length_map _
  rw [List.length_map, List.length_append] at h1
  have h4 := hT.length_le hP
  have h5 := hC.length_le
  omega

end

end Chazelle.Final
